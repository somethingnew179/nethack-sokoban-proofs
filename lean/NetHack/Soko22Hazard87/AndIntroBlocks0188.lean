import NetHack.Soko22Hazard87.AndIntroBlocks0187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro47000 (p : Pattern) (ha : d116753 p = 1) (hb : d194508 p = 1) : d197050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194503 q = 1) : d197037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194503, d197037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46999 q ha hb
    | true =>
      simp only [d194503, d197037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194504 q = 1) : d197038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194504, d197038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194504, d197038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d116753 q = 1) : d197045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d197045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46708 q ha hb
    | true =>
      simp only [d22983, d197045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d116753 q = 1) : d197046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d197046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d197046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194505 q = 1) : d197047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194505, d197047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194505, d197047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194506 q = 1) : d197048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194506, d197048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194506, d197048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194507 q = 1) : d197049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194507, d197049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194507, d197049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194508 q = 1) : d197050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194508, d197050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194508, d197050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro47001 (p : Pattern) (ha : d116753 p = 1) (hb : d194514 p = 1) : d197965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194509 q = 1) : d197960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194509, d197960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47000 q ha hb
    | true =>
      simp only [d194509, d197960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46709 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194510 q = 1) : d197961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194510, d197961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194510, d197961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194511 q = 1) : d197962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194511, d197962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194511, d197962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194512 q = 1) : d197963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194512, d197963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194512, d197963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194513 q = 1) : d197964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194513, d197964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194513, d197964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194514 q = 1) : d197965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194514, d197965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194514, d197965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47002 (p : Pattern) (ha : d116753 p = 1) (hb : d194520 p = 1) : d197971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d116753 q = 1) : d196914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d196914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46696 q ha hb
    | true =>
      simp only [d22747, d196914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46699 q ha hb
  have h2 (q : Pattern) (ha : d22748 q = 1) (hb : d116753 q = 1) : d196915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d196915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d196915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194493 q = 1) : d197952 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194493, d197952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194493, d197952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194494 q = 1) : d197953 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194494, d197953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194494, d197953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194496 q = 1) : d197955 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194496, d197955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194496, d197955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46998 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194497 q = 1) : d197956 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194497, d197956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194497, d197956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194498 q = 1) : d197957 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194498, d197957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194498, d197957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194499 q = 1) : d197958 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194499, d197958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194499, d197958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d194500 q = 1) : d197959 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194500, d197959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194500, d197959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d194515 q = 1) : d197966 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194515, d197966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194515, d197966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47001 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194516 q = 1) : d197967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194516, d197967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194516, d197967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d194517 q = 1) : d197968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194517, d197968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194517, d197968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194518 q = 1) : d197969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194518, d197969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194518, d197969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d194519 q = 1) : d197970 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194519, d197970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194519, d197970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d194520 q = 1) : d197971 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194520, d197971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194520, d197971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47003 (p : Pattern) (ha : d116753 p = 1) (hb : d194526 p = 1) : d197977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194521 q = 1) : d197972 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194521, d197972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194521, d197972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47002 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194522 q = 1) : d197973 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194522, d197973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194522, d197973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194523 q = 1) : d197974 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194523, d197974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194523, d197974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194524 q = 1) : d197975 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194524, d197975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194524, d197975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194525 q = 1) : d197976 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194525, d197976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194525, d197976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194526 q = 1) : d197977 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194526, d197977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194526, d197977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47004 (p : Pattern) (ha : d116753 p = 1) (hb : d194532 p = 1) : d197983 p = 1 := by
  have h0 (q : Pattern) (ha : d116753 q = 1) (hb : d194389 q = 1) : d197864 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194389, d197864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46977 q ha hb
    | true =>
      simp only [d194389, d197864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46981 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194416 q = 1) : d197891 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194416, d197891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194416, d197891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46985 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194417 q = 1) : d197892 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194417, d197892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194417, d197892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194452 q = 1) : d197919 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194452, d197919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194452, d197919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46991 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194453 q = 1) : d197920 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194453, d197920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194453, d197920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194454 q = 1) : d197921 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194454, d197921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194454, d197921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194489 q = 1) : d197948 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194489, d197948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194489, d197948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46997 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194490 q = 1) : d197949 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194490, d197949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194490, d197949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d194491 q = 1) : d197950 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194491, d197950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194491, d197950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d194492 q = 1) : d197951 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194492, d197951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194492, d197951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194527 q = 1) : d197978 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194527, d197978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194527, d197978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47003 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d194528 q = 1) : d197979 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194528, d197979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194528, d197979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194529 q = 1) : d197980 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194529, d197980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194529, d197980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d194530 q = 1) : d197981 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194530, d197981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194530, d197981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d194531 q = 1) : d197982 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d194531, d197982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194531, d197982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d194532 q = 1) : d197983 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d194532, d197983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194532, d197983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro47005 (p : Pattern) (ha : d116753 p = 1) (hb : d194538 p = 1) : d197989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194533 q = 1) : d197984 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d194533, d197984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47004 q ha hb
    | true =>
      simp only [d194533, d197984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194534 q = 1) : d197985 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d194534, d197985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194534, d197985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194535 q = 1) : d197986 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d194535, d197986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194535, d197986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194536 q = 1) : d197987 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d194536, d197987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194536, d197987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194537 q = 1) : d197988 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d194537, d197988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194537, d197988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194538 q = 1) : d197989 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d194538, d197989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194538, d197989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47006 (p : Pattern) (ha : d116753 p = 1) (hb : d194544 p = 1) : d197995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194539 q = 1) : d197990 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d194539, d197990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47005 q ha hb
    | true =>
      simp only [d194539, d197990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194540 q = 1) : d197991 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d194540, d197991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194540, d197991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194541 q = 1) : d197992 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d194541, d197992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194541, d197992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194542 q = 1) : d197993 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d194542, d197993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194542, d197993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194543 q = 1) : d197994 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d194543, d197994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194543, d197994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194544 q = 1) : d197995 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d194544, d197995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194544, d197995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47007 (p : Pattern) (ha : d116753 p = 1) (hb : d194550 p = 1) : d198001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194545 q = 1) : d197996 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d194545, d197996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47006 q ha hb
    | true =>
      simp only [d194545, d197996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194546 q = 1) : d197997 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d194546, d197997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194546, d197997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194547 q = 1) : d197998 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d194547, d197998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194547, d197998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194548 q = 1) : d197999 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d194548, d197999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194548, d197999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194549 q = 1) : d198000 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d194549, d198000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194549, d198000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194550 q = 1) : d198001 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d194550, d198001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194550, d198001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47008 (p : Pattern) (ha : d116753 p = 1) (hb : d194556 p = 1) : d198007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194551 q = 1) : d198002 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d194551, d198002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47007 q ha hb
    | true =>
      simp only [d194551, d198002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194552 q = 1) : d198003 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d194552, d198003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194552, d198003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194553 q = 1) : d198004 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d194553, d198004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194553, d198004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194554 q = 1) : d198005 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d194554, d198005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194554, d198005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194555 q = 1) : d198006 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d194555, d198006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194555, d198006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194556 q = 1) : d198007 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d194556, d198007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194556, d198007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47009 (p : Pattern) (ha : d116753 p = 1) (hb : d194562 p = 1) : d198013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194557 q = 1) : d198008 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d194557, d198008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47008 q ha hb
    | true =>
      simp only [d194557, d198008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194558 q = 1) : d198009 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d194558, d198009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194558, d198009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194559 q = 1) : d198010 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d194559, d198010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194559, d198010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194560 q = 1) : d198011 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d194560, d198011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194560, d198011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194561 q = 1) : d198012 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d194561, d198012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194561, d198012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194562 q = 1) : d198013 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d194562, d198013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194562, d198013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47010 (p : Pattern) (ha : d116753 p = 1) (hb : d194568 p = 1) : d198019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194563 q = 1) : d198014 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d194563, d198014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47009 q ha hb
    | true =>
      simp only [d194563, d198014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194564 q = 1) : d198015 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d194564, d198015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194564, d198015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194565 q = 1) : d198016 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d194565, d198016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194565, d198016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194566 q = 1) : d198017 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d194566, d198017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194566, d198017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194567 q = 1) : d198018 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d194567, d198018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194567, d198018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194568 q = 1) : d198019 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d194568, d198019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194568, d198019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47011 (p : Pattern) (ha : d116753 p = 1) (hb : d194574 p = 1) : d198025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194569 q = 1) : d198020 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d194569, d198020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47010 q ha hb
    | true =>
      simp only [d194569, d198020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194570 q = 1) : d198021 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d194570, d198021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194570, d198021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194571 q = 1) : d198022 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d194571, d198022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194571, d198022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194572 q = 1) : d198023 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d194572, d198023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194572, d198023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194573 q = 1) : d198024 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d194573, d198024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194573, d198024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194574 q = 1) : d198025 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d194574, d198025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194574, d198025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47012 (p : Pattern) (ha : d96325 p = 1) (hb : d120136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96320 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96321 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96321, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d96321, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96232 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96322 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96322, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96322, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96323 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96323, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96323, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96324 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96324, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96324, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96325 q = 1) (hb : d120136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96325, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96325, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47013 (p : Pattern) (ha : d96341 p = 1) (hb : d120143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96321 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96321, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96321, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96232 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96322 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96322, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96322, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96323 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96323, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96323, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96324 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96324, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96324, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d96330 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96334 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d96336 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d96238 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
    | true =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d96337 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96337, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d96337, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d96239 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d96338 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96338, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d96338, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d96339 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96339, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d96339, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96340 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96340, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d96340, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d96341 q = 1) (hb : d120143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96341, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96341, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47014 (p : Pattern) (ha : d96350 p = 1) (hb : d120334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96336 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96238 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
    | true =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96337 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96337, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96337, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96239 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96338 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96338, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96338, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96348 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96348, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96348, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96349 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96349, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96349, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96350 q = 1) (hb : d120334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96350, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96350, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47015 (p : Pattern) (ha : d96372 p = 1) (hb : d120378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96367 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96265 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96265, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46759 q ha hb
    | true =>
      simp only [d96265, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96368 q = 1) (hb : d120374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96368, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96368, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96266 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96369 q = 1) (hb : d120375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96369, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96369, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96370 q = 1) (hb : d120376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96370, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96370, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96371 q = 1) (hb : d120377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96371, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96371, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96372 q = 1) (hb : d120378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96372, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96372, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47016 (p : Pattern) (ha : d96378 p = 1) (hb : d121355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96296 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96342 q = 1) (hb : d120144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96342, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47012 q ha hb
    | true =>
      simp only [d96342, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47013 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96345 q = 1) (hb : d120145 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96345, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96345, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96346 q = 1) (hb : d121345 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96346, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96346, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96347 q = 1) (hb : d121346 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96347, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96347, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96351 q = 1) (hb : d120335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96351, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96351, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47014 q ha hb
  have h8 (q : Pattern) (ha : d96352 q = 1) (hb : d121347 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96352, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96352, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d96353 q = 1) (hb : d121348 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96353, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96353, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d96354 q = 1) (hb : d121349 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96354, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96354, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d96355 q = 1) (hb : d121350 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96355, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96355, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96373 q = 1) (hb : d120379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96373, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96373, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47015 q ha hb
  have h13 (q : Pattern) (ha : d96374 q = 1) (hb : d121351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96374, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96374, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d96375 q = 1) (hb : d121352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96375, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96375, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d96376 q = 1) (hb : d121353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96376, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d96376, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d96377 q = 1) (hb : d121354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96377, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96377, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d96378 q = 1) (hb : d121355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96378, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96378, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47017 (p : Pattern) (ha : d96384 p = 1) (hb : d121361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96281 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96379 q = 1) (hb : d121356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96379, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96379, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47016 q ha hb
  have h3 (q : Pattern) (ha : d96380 q = 1) (hb : d121357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96380, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96380, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96381 q = 1) (hb : d121358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96381, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96381, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96382 q = 1) (hb : d121359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96382, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96382, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96383 q = 1) (hb : d121360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96383, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96383, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96384 q = 1) (hb : d121361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96384, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96384, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47018 (p : Pattern) (ha : d195434 p = 1) (hb : d196146 p = 1) : d197155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195410 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d195428 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d120078 q = 1) : d120078 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d195387 q = 1) (hb : d196086 q = 1) : d197150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46784 q ha hb
    | true =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195429 q = 1) (hb : d196142 q = 1) : d197151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195429, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d195429, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d195430 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d195431 q = 1) (hb : d196143 q = 1) : d197152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195431, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195431, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d195432 q = 1) (hb : d196144 q = 1) : d197153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195432, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195432, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195433 q = 1) (hb : d196145 q = 1) : d197154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195433, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195433, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d195434 q = 1) (hb : d196146 q = 1) : d197155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195434, d196146, d197155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195434, d196146, d197155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47019 (p : Pattern) (ha : d195451 p = 1) (hb : d196153 p = 1) : d197164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195410 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195428 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120078 q = 1) : d120078 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195387 q = 1) (hb : d196086 q = 1) : d197150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46784 q ha hb
    | true =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195429 q = 1) (hb : d196142 q = 1) : d197151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195429, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195429, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d195430 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d195431 q = 1) (hb : d196143 q = 1) : d197152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195431, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195431, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d195432 q = 1) (hb : d196144 q = 1) : d197153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195432, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195432, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195433 q = 1) (hb : d196145 q = 1) : d197154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195433, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195433, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d195439 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195443 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d195445 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d120085 q = 1) : d120085 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195396 q = 1) (hb : d196093 q = 1) : d197159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195396, d196093, d197159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46786 q ha hb
    | true =>
      simp only [d195396, d196093, d197159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195446 q = 1) (hb : d196149 q = 1) : d197160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195446, d196149, d197160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d195446, d196149, d197160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d195447 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d195448 q = 1) (hb : d196150 q = 1) : d197161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195448, d196150, d197161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195448, d196150, d197161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d195449 q = 1) (hb : d196151 q = 1) : d197162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195449, d196151, d197162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d195449, d196151, d197162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d195450 q = 1) (hb : d196152 q = 1) : d197163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195450, d196152, d197163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d195450, d196152, d197163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195451 q = 1) (hb : d196153 q = 1) : d197164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195451, d196153, d197164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195451, d196153, d197164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro47020 (p : Pattern) (ha : d195460 p = 1) (hb : d197841 p = 1) : d198028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195445 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d120085 q = 1) : d120085 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195396 q = 1) (hb : d196093 q = 1) : d197159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195396, d196093, d197159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46786 q ha hb
    | true =>
      simp only [d195396, d196093, d197159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195446 q = 1) (hb : d196149 q = 1) : d197160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195446, d196149, d197160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195446, d196149, d197160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195447 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195448 q = 1) (hb : d196150 q = 1) : d197161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195448, d196150, d197161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195448, d196150, d197161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195458 q = 1) (hb : d196151 q = 1) : d197162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195458, d196151, d197162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195458, d196151, d197162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195459 q = 1) (hb : d196152 q = 1) : d197163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195459, d196152, d197163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195459, d196152, d197163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195460 q = 1) (hb : d197841 q = 1) : d198028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195460, d197841, d198028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195460, d197841, d198028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47021 (p : Pattern) (ha : d195488 p = 1) (hb : d197851 p = 1) : d198039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195481 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d120114 q = 1) : d120114 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195482 q = 1) (hb : d196124 q = 1) : d198034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195482, d196124, d198034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46809 q ha hb
    | true =>
      simp only [d195482, d196124, d198034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195483 q = 1) (hb : d197847 q = 1) : d198035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195483, d197847, d198035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195483, d197847, d198035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195484 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195485 q = 1) (hb : d197848 q = 1) : d198036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195485, d197848, d198036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195485, d197848, d198036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195486 q = 1) (hb : d197849 q = 1) : d198037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195486, d197849, d198037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195486, d197849, d198037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195487 q = 1) (hb : d197850 q = 1) : d198038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195487, d197850, d198038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195487, d197850, d198038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195488 q = 1) (hb : d197851 q = 1) : d198039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195488, d197851, d198039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195488, d197851, d198039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47022 (p : Pattern) (ha : d195494 p = 1) (hb : d197857 p = 1) : d198045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195452 q = 1) (hb : d196154 q = 1) : d197165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195452, d196154, d197165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47018 q ha hb
    | true =>
      simp only [d195452, d196154, d197165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47019 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195454 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195455 q = 1) (hb : d196155 q = 1) : d197166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195455, d196155, d197166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195455, d196155, d197166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195456 q = 1) (hb : d197839 q = 1) : d198026 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195456, d197839, d198026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195456, d197839, d198026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195457 q = 1) (hb : d197840 q = 1) : d198027 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195457, d197840, d198027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195457, d197840, d198027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195461 q = 1) (hb : d197842 q = 1) : d198029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195461, d197842, d198029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195461, d197842, d198029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47020 q ha hb
  have h8 (q : Pattern) (ha : d195462 q = 1) (hb : d197843 q = 1) : d198030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195462, d197843, d198030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195462, d197843, d198030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d195463 q = 1) (hb : d197844 q = 1) : d198031 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195463, d197844, d198031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195463, d197844, d198031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d195464 q = 1) (hb : d197845 q = 1) : d198032 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195464, d197845, d198032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195464, d197845, d198032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d195465 q = 1) (hb : d197846 q = 1) : d198033 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195465, d197846, d198033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195465, d197846, d198033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195489 q = 1) (hb : d197852 q = 1) : d198040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195489, d197852, d198040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195489, d197852, d198040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47021 q ha hb
  have h13 (q : Pattern) (ha : d195490 q = 1) (hb : d197853 q = 1) : d198041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195490, d197853, d198041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195490, d197853, d198041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d195491 q = 1) (hb : d197854 q = 1) : d198042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195491, d197854, d198042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195491, d197854, d198042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d195492 q = 1) (hb : d197855 q = 1) : d198043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195492, d197855, d198043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195492, d197855, d198043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d195493 q = 1) (hb : d197856 q = 1) : d198044 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195493, d197856, d198044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195493, d197856, d198044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d195494 q = 1) (hb : d197857 q = 1) : d198045 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195494, d197857, d198045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195494, d197857, d198045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47023 (p : Pattern) (ha : d195500 p = 1) (hb : d197863 p = 1) : d198051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195495 q = 1) (hb : d197858 q = 1) : d198046 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195495, d197858, d198046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195495, d197858, d198046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47022 q ha hb
  have h2 (q : Pattern) (ha : d195496 q = 1) (hb : d197859 q = 1) : d198047 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195496, d197859, d198047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195496, d197859, d198047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195497 q = 1) (hb : d197860 q = 1) : d198048 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195497, d197860, d198048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195497, d197860, d198048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195498 q = 1) (hb : d197861 q = 1) : d198049 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195498, d197861, d198049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195498, d197861, d198049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195499 q = 1) (hb : d197862 q = 1) : d198050 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195499, d197862, d198050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195499, d197862, d198050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195500 q = 1) (hb : d197863 q = 1) : d198051 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195500, d197863, d198051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195500, d197863, d198051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47024 (p : Pattern) (ha : d195553 p = 1) (hb : d196283 p = 1) : d197279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195535 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d195547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d120416 q = 1) : d120416 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d195506 q = 1) (hb : d196278 q = 1) : d197274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46816 q ha hb
    | true =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195548 q = 1) (hb : d196279 q = 1) : d197275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195548, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d195548, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d195549 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d195550 q = 1) (hb : d196280 q = 1) : d197276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195550, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195550, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d195551 q = 1) (hb : d196281 q = 1) : d197277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195551, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195551, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195552 q = 1) (hb : d196282 q = 1) : d197278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195552, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195552, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d195553 q = 1) (hb : d196283 q = 1) : d197279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195553, d196283, d197279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195553, d196283, d197279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47025 (p : Pattern) (ha : d195570 p = 1) (hb : d196292 p = 1) : d197288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195529 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195535 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120416 q = 1) : d120416 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195506 q = 1) (hb : d196278 q = 1) : d197274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46816 q ha hb
    | true =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195548 q = 1) (hb : d196279 q = 1) : d197275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195548, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195548, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d195549 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d195550 q = 1) (hb : d196280 q = 1) : d197276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195550, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195550, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d195551 q = 1) (hb : d196281 q = 1) : d197277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195551, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195551, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195552 q = 1) (hb : d196282 q = 1) : d197278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195552, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195552, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d195558 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195562 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d195564 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d120426 q = 1) : d120426 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195515 q = 1) (hb : d196287 q = 1) : d197283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195515, d196287, d197283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46818 q ha hb
    | true =>
      simp only [d195515, d196287, d197283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195565 q = 1) (hb : d196288 q = 1) : d197284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195565, d196288, d197284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d195565, d196288, d197284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d195566 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d195567 q = 1) (hb : d196289 q = 1) : d197285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195567, d196289, d197285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195567, d196289, d197285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d195568 q = 1) (hb : d196290 q = 1) : d197286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195568, d196290, d197286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d195568, d196290, d197286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d195569 q = 1) (hb : d196291 q = 1) : d197287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195569, d196291, d197287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d195569, d196291, d197287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195570 q = 1) (hb : d196292 q = 1) : d197288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195570, d196292, d197288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195570, d196292, d197288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro47026 (p : Pattern) (ha : d195579 p = 1) (hb : d197867 p = 1) : d198055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195564 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d120426 q = 1) : d120426 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195515 q = 1) (hb : d196287 q = 1) : d197283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195515, d196287, d197283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46818 q ha hb
    | true =>
      simp only [d195515, d196287, d197283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195565 q = 1) (hb : d196288 q = 1) : d197284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195565, d196288, d197284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195565, d196288, d197284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195566 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195567 q = 1) (hb : d196289 q = 1) : d197285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195567, d196289, d197285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195567, d196289, d197285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195577 q = 1) (hb : d196290 q = 1) : d197286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195577, d196290, d197286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195577, d196290, d197286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195578 q = 1) (hb : d196291 q = 1) : d197287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195578, d196291, d197287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195578, d196291, d197287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195579 q = 1) (hb : d197867 q = 1) : d198055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195579, d197867, d198055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195579, d197867, d198055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47027 (p : Pattern) (ha : d195607 p = 1) (hb : d197878 p = 1) : d198066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195600 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d120594 q = 1) : d120594 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195601 q = 1) (hb : d197873 q = 1) : d198061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195601, d197873, d198061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46842 q ha hb
    | true =>
      simp only [d195601, d197873, d198061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195602 q = 1) (hb : d197874 q = 1) : d198062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195602, d197874, d198062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195602, d197874, d198062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195604 q = 1) (hb : d197875 q = 1) : d198063 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195604, d197875, d198063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195604, d197875, d198063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195605 q = 1) (hb : d197876 q = 1) : d198064 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195605, d197876, d198064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195605, d197876, d198064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195606 q = 1) (hb : d197877 q = 1) : d198065 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195606, d197877, d198065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195606, d197877, d198065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195607 q = 1) (hb : d197878 q = 1) : d198066 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195607, d197878, d198066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195607, d197878, d198066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47028 (p : Pattern) (ha : d195613 p = 1) (hb : d197884 p = 1) : d198072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195523 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195571 q = 1) (hb : d196293 q = 1) : d197289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195571, d196293, d197289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47024 q ha hb
    | true =>
      simp only [d195571, d196293, d197289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47025 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195573 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195574 q = 1) (hb : d196294 q = 1) : d197290 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195574, d196294, d197290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195574, d196294, d197290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195575 q = 1) (hb : d197865 q = 1) : d198053 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195575, d197865, d198053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195575, d197865, d198053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195576 q = 1) (hb : d197866 q = 1) : d198054 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195576, d197866, d198054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195576, d197866, d198054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195580 q = 1) (hb : d197868 q = 1) : d198056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195580, d197868, d198056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195580, d197868, d198056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47026 q ha hb
  have h8 (q : Pattern) (ha : d195581 q = 1) (hb : d197869 q = 1) : d198057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195581, d197869, d198057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195581, d197869, d198057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d195582 q = 1) (hb : d197870 q = 1) : d198058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195582, d197870, d198058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195582, d197870, d198058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d195583 q = 1) (hb : d197871 q = 1) : d198059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195583, d197871, d198059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195583, d197871, d198059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d195584 q = 1) (hb : d197872 q = 1) : d198060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195584, d197872, d198060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195584, d197872, d198060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195608 q = 1) (hb : d197879 q = 1) : d198067 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195608, d197879, d198067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195608, d197879, d198067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47027 q ha hb
  have h13 (q : Pattern) (ha : d195609 q = 1) (hb : d197880 q = 1) : d198068 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195609, d197880, d198068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195609, d197880, d198068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d195610 q = 1) (hb : d197881 q = 1) : d198069 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195610, d197881, d198069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195610, d197881, d198069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d195611 q = 1) (hb : d197882 q = 1) : d198070 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195611, d197882, d198070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195611, d197882, d198070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d195612 q = 1) (hb : d197883 q = 1) : d198071 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195612, d197883, d198071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195612, d197883, d198071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d195613 q = 1) (hb : d197884 q = 1) : d198072 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195613, d197884, d198072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195613, d197884, d198072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47029 (p : Pattern) (ha : d195619 p = 1) (hb : d197890 p = 1) : d198078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195614 q = 1) (hb : d197885 q = 1) : d198073 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195614, d197885, d198073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195614, d197885, d198073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47028 q ha hb
  have h2 (q : Pattern) (ha : d195615 q = 1) (hb : d197886 q = 1) : d198074 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195615, d197886, d198074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195615, d197886, d198074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195616 q = 1) (hb : d197887 q = 1) : d198075 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195616, d197887, d198075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195616, d197887, d198075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195617 q = 1) (hb : d197888 q = 1) : d198076 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195617, d197888, d198076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195617, d197888, d198076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195618 q = 1) (hb : d197889 q = 1) : d198077 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195618, d197889, d198077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195618, d197889, d198077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195619 q = 1) (hb : d197890 q = 1) : d198078 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195619, d197890, d198078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195619, d197890, d198078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47030 (p : Pattern) (ha : d195680 p = 1) (hb : d196450 p = 1) : d197404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195656 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195662 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d195674 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d196444 q = 1) : d196444 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d195633 q = 1) (hb : d196445 q = 1) : d197399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46853 q ha hb
    | true =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195675 q = 1) (hb : d196446 q = 1) : d197400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195675, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d195675, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d195676 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d195677 q = 1) (hb : d196447 q = 1) : d197401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195677, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195677, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d195678 q = 1) (hb : d196448 q = 1) : d197402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195678, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195678, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195679 q = 1) (hb : d196449 q = 1) : d197403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195679, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195679, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d195680 q = 1) (hb : d196450 q = 1) : d197404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195680, d196450, d197404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195680, d196450, d197404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47031 (p : Pattern) (ha : d195697 p = 1) (hb : d196460 p = 1) : d197413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195656 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196444 q = 1) : d196444 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195633 q = 1) (hb : d196445 q = 1) : d197399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46853 q ha hb
    | true =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195675 q = 1) (hb : d196446 q = 1) : d197400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195675, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195675, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d195676 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d195677 q = 1) (hb : d196447 q = 1) : d197401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195677, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195677, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d195678 q = 1) (hb : d196448 q = 1) : d197402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195678, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195678, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195679 q = 1) (hb : d196449 q = 1) : d197403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195679, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195679, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d195685 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195689 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d195691 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d196454 q = 1) : d196454 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195642 q = 1) (hb : d196455 q = 1) : d197408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195642, d196455, d197408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46855 q ha hb
    | true =>
      simp only [d195642, d196455, d197408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195692 q = 1) (hb : d196456 q = 1) : d197409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195692, d196456, d197409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d195692, d196456, d197409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d195693 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d195694 q = 1) (hb : d196457 q = 1) : d197410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195694, d196457, d197410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195694, d196457, d197410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d195695 q = 1) (hb : d196458 q = 1) : d197411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195695, d196458, d197411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d195695, d196458, d197411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d195696 q = 1) (hb : d196459 q = 1) : d197412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195696, d196459, d197412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d195696, d196459, d197412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195697 q = 1) (hb : d196460 q = 1) : d197413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195697, d196460, d197413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195697, d196460, d197413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro47032 (p : Pattern) (ha : d195706 p = 1) (hb : d197895 p = 1) : d198083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d196454 q = 1) : d196454 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195642 q = 1) (hb : d196455 q = 1) : d197408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195642, d196455, d197408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46855 q ha hb
    | true =>
      simp only [d195642, d196455, d197408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195692 q = 1) (hb : d196456 q = 1) : d197409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195692, d196456, d197409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195692, d196456, d197409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195693 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195694 q = 1) (hb : d196457 q = 1) : d197410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195694, d196457, d197410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195694, d196457, d197410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195704 q = 1) (hb : d196458 q = 1) : d197411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195704, d196458, d197411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195704, d196458, d197411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195705 q = 1) (hb : d196459 q = 1) : d197412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195705, d196459, d197412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195705, d196459, d197412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195706 q = 1) (hb : d197895 q = 1) : d198083 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195706, d197895, d198083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195706, d197895, d198083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47033 (p : Pattern) (ha : d195741 p = 1) (hb : d197906 p = 1) : d198094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d196622 q = 1) : d196622 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195735 q = 1) (hb : d197901 q = 1) : d198089 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195735, d197901, d198089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46882 q ha hb
    | true =>
      simp only [d195735, d197901, d198089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195736 q = 1) (hb : d197902 q = 1) : d198090 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195736, d197902, d198090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195736, d197902, d198090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195737 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195738 q = 1) (hb : d197903 q = 1) : d198091 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195738, d197903, d198091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195738, d197903, d198091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195739 q = 1) (hb : d197904 q = 1) : d198092 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195739, d197904, d198092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195739, d197904, d198092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195740 q = 1) (hb : d197905 q = 1) : d198093 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195740, d197905, d198093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195740, d197905, d198093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195741 q = 1) (hb : d197906 q = 1) : d198094 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195741, d197906, d198094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195741, d197906, d198094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47034 (p : Pattern) (ha : d195747 p = 1) (hb : d197912 p = 1) : d198100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195698 q = 1) (hb : d196461 q = 1) : d197414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195698, d196461, d197414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47030 q ha hb
    | true =>
      simp only [d195698, d196461, d197414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47031 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195700 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195701 q = 1) (hb : d196462 q = 1) : d197415 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195701, d196462, d197415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195701, d196462, d197415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195702 q = 1) (hb : d197893 q = 1) : d198081 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195702, d197893, d198081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195702, d197893, d198081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195703 q = 1) (hb : d197894 q = 1) : d198082 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195703, d197894, d198082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195703, d197894, d198082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195707 q = 1) (hb : d197896 q = 1) : d198084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195707, d197896, d198084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195707, d197896, d198084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47032 q ha hb
  have h8 (q : Pattern) (ha : d195708 q = 1) (hb : d197897 q = 1) : d198085 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195708, d197897, d198085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195708, d197897, d198085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d195709 q = 1) (hb : d197898 q = 1) : d198086 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195709, d197898, d198086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195709, d197898, d198086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d195710 q = 1) (hb : d197899 q = 1) : d198087 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195710, d197899, d198087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195710, d197899, d198087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d195711 q = 1) (hb : d197900 q = 1) : d198088 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195711, d197900, d198088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195711, d197900, d198088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195742 q = 1) (hb : d197907 q = 1) : d198095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195742, d197907, d198095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195742, d197907, d198095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47033 q ha hb
  have h13 (q : Pattern) (ha : d195743 q = 1) (hb : d197908 q = 1) : d198096 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195743, d197908, d198096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195743, d197908, d198096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d195744 q = 1) (hb : d197909 q = 1) : d198097 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195744, d197909, d198097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195744, d197909, d198097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d195745 q = 1) (hb : d197910 q = 1) : d198098 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195745, d197910, d198098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195745, d197910, d198098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d195746 q = 1) (hb : d197911 q = 1) : d198099 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195746, d197911, d198099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195746, d197911, d198099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d195747 q = 1) (hb : d197912 q = 1) : d198100 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195747, d197912, d198100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195747, d197912, d198100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47035 (p : Pattern) (ha : d195753 p = 1) (hb : d197918 p = 1) : d198106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195748 q = 1) (hb : d197913 q = 1) : d198101 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195748, d197913, d198101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195748, d197913, d198101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47034 q ha hb
  have h2 (q : Pattern) (ha : d195749 q = 1) (hb : d197914 q = 1) : d198102 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195749, d197914, d198102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195749, d197914, d198102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195750 q = 1) (hb : d197915 q = 1) : d198103 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195750, d197915, d198103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195750, d197915, d198103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195751 q = 1) (hb : d197916 q = 1) : d198104 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195751, d197916, d198104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195751, d197916, d198104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195752 q = 1) (hb : d197917 q = 1) : d198105 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195752, d197917, d198105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195752, d197917, d198105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195753 q = 1) (hb : d197918 q = 1) : d198106 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195753, d197918, d198106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195753, d197918, d198106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47036 (p : Pattern) (ha : d195815 p = 1) (hb : d196676 p = 1) : d197538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d195809 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d196670 q = 1) : d196670 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d195768 q = 1) (hb : d196671 q = 1) : d197533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46894 q ha hb
    | true =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195810 q = 1) (hb : d196672 q = 1) : d197534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195810, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d195810, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d195811 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d195812 q = 1) (hb : d196673 q = 1) : d197535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195812, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195812, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d195813 q = 1) (hb : d196674 q = 1) : d197536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195813, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195813, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195814 q = 1) (hb : d196675 q = 1) : d197537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195814, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195814, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d195815 q = 1) (hb : d196676 q = 1) : d197538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195815, d196676, d197538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195815, d196676, d197538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47037 (p : Pattern) (ha : d195832 p = 1) (hb : d196686 p = 1) : d197547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195791 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196670 q = 1) : d196670 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195768 q = 1) (hb : d196671 q = 1) : d197533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46894 q ha hb
    | true =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195810 q = 1) (hb : d196672 q = 1) : d197534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195810, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195810, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d195811 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d195812 q = 1) (hb : d196673 q = 1) : d197535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195812, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195812, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d195813 q = 1) (hb : d196674 q = 1) : d197536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195813, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195813, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195814 q = 1) (hb : d196675 q = 1) : d197537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195814, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195814, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d195820 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195824 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d195826 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d196680 q = 1) : d196680 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195777 q = 1) (hb : d196681 q = 1) : d197542 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195777, d196681, d197542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46896 q ha hb
    | true =>
      simp only [d195777, d196681, d197542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195827 q = 1) (hb : d196682 q = 1) : d197543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195827, d196682, d197543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d195827, d196682, d197543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d195828 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d195829 q = 1) (hb : d196683 q = 1) : d197544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195829, d196683, d197544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195829, d196683, d197544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d195830 q = 1) (hb : d196684 q = 1) : d197545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195830, d196684, d197545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d195830, d196684, d197545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d195831 q = 1) (hb : d196685 q = 1) : d197546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195831, d196685, d197546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d195831, d196685, d197546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195832 q = 1) (hb : d196686 q = 1) : d197547 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195832, d196686, d197547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195832, d196686, d197547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro47038 (p : Pattern) (ha : d195841 p = 1) (hb : d197924 p = 1) : d198112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d196680 q = 1) : d196680 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195777 q = 1) (hb : d196681 q = 1) : d197542 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195777, d196681, d197542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46896 q ha hb
    | true =>
      simp only [d195777, d196681, d197542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195827 q = 1) (hb : d196682 q = 1) : d197543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195827, d196682, d197543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195827, d196682, d197543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195828 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195829 q = 1) (hb : d196683 q = 1) : d197544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195829, d196683, d197544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195829, d196683, d197544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195839 q = 1) (hb : d196684 q = 1) : d197545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195839, d196684, d197545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195839, d196684, d197545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195840 q = 1) (hb : d196685 q = 1) : d197546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195840, d196685, d197546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195840, d196685, d197546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195841 q = 1) (hb : d197924 q = 1) : d198112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195841, d197924, d198112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195841, d197924, d198112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47039 (p : Pattern) (ha : d195876 p = 1) (hb : d197935 p = 1) : d198123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d196848 q = 1) : d196848 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195870 q = 1) (hb : d197930 q = 1) : d198118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195870, d197930, d198118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46922 q ha hb
    | true =>
      simp only [d195870, d197930, d198118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195871 q = 1) (hb : d197931 q = 1) : d198119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195871, d197931, d198119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195871, d197931, d198119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195872 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195873 q = 1) (hb : d197932 q = 1) : d198120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195873, d197932, d198120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195873, d197932, d198120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195874 q = 1) (hb : d197933 q = 1) : d198121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195874, d197933, d198121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195874, d197933, d198121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195875 q = 1) (hb : d197934 q = 1) : d198122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195875, d197934, d198122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195875, d197934, d198122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195876 q = 1) (hb : d197935 q = 1) : d198123 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195876, d197935, d198123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195876, d197935, d198123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47040 (p : Pattern) (ha : d195882 p = 1) (hb : d197941 p = 1) : d198129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195785 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195833 q = 1) (hb : d196687 q = 1) : d197548 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195833, d196687, d197548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47036 q ha hb
    | true =>
      simp only [d195833, d196687, d197548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47037 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195836 q = 1) (hb : d196688 q = 1) : d197549 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195836, d196688, d197549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195836, d196688, d197549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195837 q = 1) (hb : d197922 q = 1) : d198110 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195837, d197922, d198110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195837, d197922, d198110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195838 q = 1) (hb : d197923 q = 1) : d198111 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195838, d197923, d198111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195838, d197923, d198111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195842 q = 1) (hb : d197925 q = 1) : d198113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195842, d197925, d198113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195842, d197925, d198113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47038 q ha hb
  have h8 (q : Pattern) (ha : d195843 q = 1) (hb : d197926 q = 1) : d198114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195843, d197926, d198114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195843, d197926, d198114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d195844 q = 1) (hb : d197927 q = 1) : d198115 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195844, d197927, d198115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195844, d197927, d198115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d195845 q = 1) (hb : d197928 q = 1) : d198116 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195845, d197928, d198116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195845, d197928, d198116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d195846 q = 1) (hb : d197929 q = 1) : d198117 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195846, d197929, d198117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195846, d197929, d198117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195877 q = 1) (hb : d197936 q = 1) : d198124 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195877, d197936, d198124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195877, d197936, d198124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47039 q ha hb
  have h13 (q : Pattern) (ha : d195878 q = 1) (hb : d197937 q = 1) : d198125 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195878, d197937, d198125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195878, d197937, d198125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d195879 q = 1) (hb : d197938 q = 1) : d198126 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195879, d197938, d198126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195879, d197938, d198126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d195880 q = 1) (hb : d197939 q = 1) : d198127 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195880, d197939, d198127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195880, d197939, d198127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d195881 q = 1) (hb : d197940 q = 1) : d198128 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195881, d197940, d198128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195881, d197940, d198128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d195882 q = 1) (hb : d197941 q = 1) : d198129 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195882, d197941, d198129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195882, d197941, d198129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47041 (p : Pattern) (ha : d195888 p = 1) (hb : d197947 p = 1) : d198135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195883 q = 1) (hb : d197942 q = 1) : d198130 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195883, d197942, d198130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195883, d197942, d198130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47040 q ha hb
  have h2 (q : Pattern) (ha : d195884 q = 1) (hb : d197943 q = 1) : d198131 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195884, d197943, d198131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195884, d197943, d198131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195885 q = 1) (hb : d197944 q = 1) : d198132 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195885, d197944, d198132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195885, d197944, d198132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195886 q = 1) (hb : d197945 q = 1) : d198133 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195886, d197945, d198133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195886, d197945, d198133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195887 q = 1) (hb : d197946 q = 1) : d198134 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195887, d197946, d198134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195887, d197946, d198134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195888 q = 1) (hb : d197947 q = 1) : d198135 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195888, d197947, d198135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195888, d197947, d198135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47042 (p : Pattern) (ha : d195951 p = 1) (hb : d196903 p = 1) : d197673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195927 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d195945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d196897 q = 1) : d196897 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d195904 q = 1) (hb : d196898 q = 1) : d197668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46933 q ha hb
    | true =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195946 q = 1) (hb : d196899 q = 1) : d197669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195946, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d195946, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d195947 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d195948 q = 1) (hb : d196900 q = 1) : d197670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195948, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195948, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d195949 q = 1) (hb : d196901 q = 1) : d197671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195949, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195949, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195950 q = 1) (hb : d196902 q = 1) : d197672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195950, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195950, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d195951 q = 1) (hb : d196903 q = 1) : d197673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195951, d196903, d197673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195951, d196903, d197673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47043 (p : Pattern) (ha : d195968 p = 1) (hb : d196913 p = 1) : d197682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195927 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196897 q = 1) : d196897 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195904 q = 1) (hb : d196898 q = 1) : d197668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46933 q ha hb
    | true =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195946 q = 1) (hb : d196899 q = 1) : d197669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195946, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d195946, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d195947 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d195948 q = 1) (hb : d196900 q = 1) : d197670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195948, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195948, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d195949 q = 1) (hb : d196901 q = 1) : d197671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195949, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195949, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195950 q = 1) (hb : d196902 q = 1) : d197672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195950, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195950, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d195956 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195960 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d195962 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d196907 q = 1) : d196907 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195913 q = 1) (hb : d196908 q = 1) : d197677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195913, d196908, d197677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46935 q ha hb
    | true =>
      simp only [d195913, d196908, d197677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195963 q = 1) (hb : d196909 q = 1) : d197678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195963, d196909, d197678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d195963, d196909, d197678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d195964 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d195965 q = 1) (hb : d196910 q = 1) : d197679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195965, d196910, d197679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195965, d196910, d197679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d195966 q = 1) (hb : d196911 q = 1) : d197680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195966, d196911, d197680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d195966, d196911, d197680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d195967 q = 1) (hb : d196912 q = 1) : d197681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195967, d196912, d197681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d195967, d196912, d197681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195968 q = 1) (hb : d196913 q = 1) : d197682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195968, d196913, d197682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195968, d196913, d197682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro47044 (p : Pattern) (ha : d195977 p = 1) (hb : d197954 p = 1) : d198142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195962 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d196907 q = 1) : d196907 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d195913 q = 1) (hb : d196908 q = 1) : d197677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195913, d196908, d197677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46935 q ha hb
    | true =>
      simp only [d195913, d196908, d197677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195963 q = 1) (hb : d196909 q = 1) : d197678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195963, d196909, d197678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195963, d196909, d197678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195964 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d195965 q = 1) (hb : d196910 q = 1) : d197679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195965, d196910, d197679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195965, d196910, d197679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d195975 q = 1) (hb : d196911 q = 1) : d197680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195975, d196911, d197680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195975, d196911, d197680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195976 q = 1) (hb : d196912 q = 1) : d197681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195976, d196912, d197681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195976, d196912, d197681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195977 q = 1) (hb : d197954 q = 1) : d198142 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195977, d197954, d198142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195977, d197954, d198142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47045 (p : Pattern) (ha : d196012 p = 1) (hb : d197965 p = 1) : d198153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d196005 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d197075 q = 1) : d197075 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d196006 q = 1) (hb : d197960 q = 1) : d198148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d196006, d197960, d198148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46960 q ha hb
    | true =>
      simp only [d196006, d197960, d198148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d196007 q = 1) (hb : d197961 q = 1) : d198149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196007, d197961, d198149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196007, d197961, d198149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d196008 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d196009 q = 1) (hb : d197962 q = 1) : d198150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196009, d197962, d198150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196009, d197962, d198150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d196010 q = 1) (hb : d197963 q = 1) : d198151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196010, d197963, d198151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196010, d197963, d198151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196011 q = 1) (hb : d197964 q = 1) : d198152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196011, d197964, d198152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196011, d197964, d198152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d196012 q = 1) (hb : d197965 q = 1) : d198153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196012, d197965, d198153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196012, d197965, d198153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47046 (p : Pattern) (ha : d196018 p = 1) (hb : d197971 p = 1) : d198159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195921 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195969 q = 1) (hb : d196914 q = 1) : d197683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195969, d196914, d197683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47042 q ha hb
    | true =>
      simp only [d195969, d196914, d197683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47043 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195971 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195972 q = 1) (hb : d196915 q = 1) : d197684 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195972, d196915, d197684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195972, d196915, d197684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195973 q = 1) (hb : d197952 q = 1) : d198140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195973, d197952, d198140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195973, d197952, d198140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195974 q = 1) (hb : d197953 q = 1) : d198141 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195974, d197953, d198141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195974, d197953, d198141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195978 q = 1) (hb : d197955 q = 1) : d198143 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195978, d197955, d198143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d195978, d197955, d198143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47044 q ha hb
  have h8 (q : Pattern) (ha : d195979 q = 1) (hb : d197956 q = 1) : d198144 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195979, d197956, d198144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195979, d197956, d198144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d195980 q = 1) (hb : d197957 q = 1) : d198145 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195980, d197957, d198145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195980, d197957, d198145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d195981 q = 1) (hb : d197958 q = 1) : d198146 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195981, d197958, d198146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195981, d197958, d198146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d195982 q = 1) (hb : d197959 q = 1) : d198147 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195982, d197959, d198147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195982, d197959, d198147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d196013 q = 1) (hb : d197966 q = 1) : d198154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d196013, d197966, d198154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d196013, d197966, d198154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47045 q ha hb
  have h13 (q : Pattern) (ha : d196014 q = 1) (hb : d197967 q = 1) : d198155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d196014, d197967, d198155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d196014, d197967, d198155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d196015 q = 1) (hb : d197968 q = 1) : d198156 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d196015, d197968, d198156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d196015, d197968, d198156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d196016 q = 1) (hb : d197969 q = 1) : d198157 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d196016, d197969, d198157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d196016, d197969, d198157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d196017 q = 1) (hb : d197970 q = 1) : d198158 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d196017, d197970, d198158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d196017, d197970, d198158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d196018 q = 1) (hb : d197971 q = 1) : d198159 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d196018, d197971, d198159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d196018, d197971, d198159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47047 (p : Pattern) (ha : d196024 p = 1) (hb : d197977 p = 1) : d198165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196019 q = 1) (hb : d197972 q = 1) : d198160 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d196019, d197972, d198160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196019, d197972, d198160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47046 q ha hb
  have h2 (q : Pattern) (ha : d196020 q = 1) (hb : d197973 q = 1) : d198161 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d196020, d197973, d198161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196020, d197973, d198161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d196021 q = 1) (hb : d197974 q = 1) : d198162 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d196021, d197974, d198162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196021, d197974, d198162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d196022 q = 1) (hb : d197975 q = 1) : d198163 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d196022, d197975, d198163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196022, d197975, d198163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d196023 q = 1) (hb : d197976 q = 1) : d198164 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d196023, d197976, d198164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196023, d197976, d198164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d196024 q = 1) (hb : d197977 q = 1) : d198165 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d196024, d197977, d198165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196024, d197977, d198165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47048 (p : Pattern) (ha : d196030 p = 1) (hb : d197983 p = 1) : d198171 p = 1 := by
  have h0 (q : Pattern) (ha : d195501 q = 1) (hb : d197864 q = 1) : d198052 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195501, d197864, d198052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47017 q ha hb
    | true =>
      simp only [d195501, d197864, d198052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47023 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d195620 q = 1) (hb : d197891 q = 1) : d198079 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195620, d197891, d198079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195620, d197891, d198079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47029 q ha hb
  have h3 (q : Pattern) (ha : d195621 q = 1) (hb : d197892 q = 1) : d198080 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195621, d197892, d198080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d195621, d197892, d198080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195754 q = 1) (hb : d197919 q = 1) : d198107 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195754, d197919, d198107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195754, d197919, d198107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47035 q ha hb
  have h5 (q : Pattern) (ha : d195755 q = 1) (hb : d197920 q = 1) : d198108 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195755, d197920, d198108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195755, d197920, d198108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195756 q = 1) (hb : d197921 q = 1) : d198109 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195756, d197921, d198109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195756, d197921, d198109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195889 q = 1) (hb : d197948 q = 1) : d198136 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195889, d197948, d198136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195889, d197948, d198136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47041 q ha hb
  have h8 (q : Pattern) (ha : d195890 q = 1) (hb : d197949 q = 1) : d198137 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195890, d197949, d198137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195890, d197949, d198137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195891 q = 1) (hb : d197950 q = 1) : d198138 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195891, d197950, d198138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195891, d197950, d198138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195892 q = 1) (hb : d197951 q = 1) : d198139 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d195892, d197951, d198139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195892, d197951, d198139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d196025 q = 1) (hb : d197978 q = 1) : d198166 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d196025, d197978, d198166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196025, d197978, d198166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47047 q ha hb
  have h12 (q : Pattern) (ha : d196026 q = 1) (hb : d197979 q = 1) : d198167 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d196026, d197979, d198167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196026, d197979, d198167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d196027 q = 1) (hb : d197980 q = 1) : d198168 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d196027, d197980, d198168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196027, d197980, d198168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d196028 q = 1) (hb : d197981 q = 1) : d198169 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d196028, d197981, d198169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196028, d197981, d198169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d196029 q = 1) (hb : d197982 q = 1) : d198170 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d196029, d197982, d198170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d196029, d197982, d198170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d196030 q = 1) (hb : d197983 q = 1) : d198171 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d196030, d197983, d198171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d196030, d197983, d198171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro47049 (p : Pattern) (ha : d196036 p = 1) (hb : d197989 p = 1) : d198177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196031 q = 1) (hb : d197984 q = 1) : d198172 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d196031, d197984, d198172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47048 q ha hb
    | true =>
      simp only [d196031, d197984, d198172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196032 q = 1) (hb : d197985 q = 1) : d198173 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d196032, d197985, d198173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196032, d197985, d198173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196033 q = 1) (hb : d197986 q = 1) : d198174 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d196033, d197986, d198174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196033, d197986, d198174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196034 q = 1) (hb : d197987 q = 1) : d198175 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d196034, d197987, d198175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196034, d197987, d198175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196035 q = 1) (hb : d197988 q = 1) : d198176 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d196035, d197988, d198176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196035, d197988, d198176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196036 q = 1) (hb : d197989 q = 1) : d198177 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d196036, d197989, d198177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196036, d197989, d198177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47050 (p : Pattern) (ha : d196042 p = 1) (hb : d197995 p = 1) : d198183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196037 q = 1) (hb : d197990 q = 1) : d198178 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d196037, d197990, d198178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47049 q ha hb
    | true =>
      simp only [d196037, d197990, d198178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196038 q = 1) (hb : d197991 q = 1) : d198179 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d196038, d197991, d198179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196038, d197991, d198179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196039 q = 1) (hb : d197992 q = 1) : d198180 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d196039, d197992, d198180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196039, d197992, d198180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196040 q = 1) (hb : d197993 q = 1) : d198181 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d196040, d197993, d198181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196040, d197993, d198181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196041 q = 1) (hb : d197994 q = 1) : d198182 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d196041, d197994, d198182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196041, d197994, d198182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196042 q = 1) (hb : d197995 q = 1) : d198183 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d196042, d197995, d198183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196042, d197995, d198183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47051 (p : Pattern) (ha : d196048 p = 1) (hb : d198001 p = 1) : d198189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196043 q = 1) (hb : d197996 q = 1) : d198184 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d196043, d197996, d198184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47050 q ha hb
    | true =>
      simp only [d196043, d197996, d198184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196044 q = 1) (hb : d197997 q = 1) : d198185 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d196044, d197997, d198185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196044, d197997, d198185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196045 q = 1) (hb : d197998 q = 1) : d198186 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d196045, d197998, d198186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196045, d197998, d198186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196046 q = 1) (hb : d197999 q = 1) : d198187 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d196046, d197999, d198187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196046, d197999, d198187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196047 q = 1) (hb : d198000 q = 1) : d198188 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d196047, d198000, d198188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196047, d198000, d198188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196048 q = 1) (hb : d198001 q = 1) : d198189 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d196048, d198001, d198189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196048, d198001, d198189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47052 (p : Pattern) (ha : d196054 p = 1) (hb : d198007 p = 1) : d198195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196049 q = 1) (hb : d198002 q = 1) : d198190 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d196049, d198002, d198190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47051 q ha hb
    | true =>
      simp only [d196049, d198002, d198190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196050 q = 1) (hb : d198003 q = 1) : d198191 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d196050, d198003, d198191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196050, d198003, d198191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196051 q = 1) (hb : d198004 q = 1) : d198192 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d196051, d198004, d198192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196051, d198004, d198192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196052 q = 1) (hb : d198005 q = 1) : d198193 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d196052, d198005, d198193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196052, d198005, d198193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196053 q = 1) (hb : d198006 q = 1) : d198194 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d196053, d198006, d198194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196053, d198006, d198194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196054 q = 1) (hb : d198007 q = 1) : d198195 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d196054, d198007, d198195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196054, d198007, d198195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47053 (p : Pattern) (ha : d196060 p = 1) (hb : d198013 p = 1) : d198201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196055 q = 1) (hb : d198008 q = 1) : d198196 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d196055, d198008, d198196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47052 q ha hb
    | true =>
      simp only [d196055, d198008, d198196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196056 q = 1) (hb : d198009 q = 1) : d198197 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d196056, d198009, d198197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196056, d198009, d198197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196057 q = 1) (hb : d198010 q = 1) : d198198 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d196057, d198010, d198198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196057, d198010, d198198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196058 q = 1) (hb : d198011 q = 1) : d198199 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d196058, d198011, d198199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196058, d198011, d198199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196059 q = 1) (hb : d198012 q = 1) : d198200 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d196059, d198012, d198200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196059, d198012, d198200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196060 q = 1) (hb : d198013 q = 1) : d198201 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d196060, d198013, d198201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196060, d198013, d198201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47054 (p : Pattern) (ha : d196066 p = 1) (hb : d198019 p = 1) : d198207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196061 q = 1) (hb : d198014 q = 1) : d198202 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d196061, d198014, d198202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47053 q ha hb
    | true =>
      simp only [d196061, d198014, d198202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196062 q = 1) (hb : d198015 q = 1) : d198203 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d196062, d198015, d198203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196062, d198015, d198203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196063 q = 1) (hb : d198016 q = 1) : d198204 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d196063, d198016, d198204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196063, d198016, d198204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196064 q = 1) (hb : d198017 q = 1) : d198205 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d196064, d198017, d198205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196064, d198017, d198205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196065 q = 1) (hb : d198018 q = 1) : d198206 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d196065, d198018, d198206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196065, d198018, d198206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196066 q = 1) (hb : d198019 q = 1) : d198207 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d196066, d198019, d198207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196066, d198019, d198207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47055 (p : Pattern) (ha : d196072 p = 1) (hb : d198025 p = 1) : d198213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196067 q = 1) (hb : d198020 q = 1) : d198208 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d196067, d198020, d198208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47054 q ha hb
    | true =>
      simp only [d196067, d198020, d198208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196068 q = 1) (hb : d198021 q = 1) : d198209 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d196068, d198021, d198209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196068, d198021, d198209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196069 q = 1) (hb : d198022 q = 1) : d198210 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d196069, d198022, d198210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196069, d198022, d198210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196070 q = 1) (hb : d198023 q = 1) : d198211 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d196070, d198023, d198211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196070, d198023, d198211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196071 q = 1) (hb : d198024 q = 1) : d198212 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d196071, d198024, d198212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196071, d198024, d198212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196072 q = 1) (hb : d198025 q = 1) : d198213 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d196072, d198025, d198213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196072, d198025, d198213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47056 (p : Pattern) (ha : d98500 p = 1) (hb : d120136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94839 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94845 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94857 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d98496 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d98496, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d98496, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94769 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d98497 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d98497, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d98497, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d98498 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d98498, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d98498, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d98499 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d98499, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d98499, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d98500 q = 1) (hb : d120136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d98500, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98500, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47057 (p : Pattern) (ha : d98505 p = 1) (hb : d120143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94839 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94857 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d98496 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d98496, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d98496, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d94769 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d98497 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d98497, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d98497, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d98498 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d98498, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d98498, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d98499 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d98499, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98499, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94879 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d94883 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d94885 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d98501 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d98501, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d98501, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d94776 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d98502 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d98502, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d98502, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d98503 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d98503, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d98503, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d98504 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d98504, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d98504, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d98505 q = 1) (hb : d120143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d98505, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d98505, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47058 (p : Pattern) (ha : d98512 p = 1) (hb : d120334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94885 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d98501 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d98501, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d98501, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d98502 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d98502, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d98502, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d98510 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d98510, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98510, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d98511 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d98511, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98511, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d98512 q = 1) (hb : d120334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d98512, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98512, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47059 (p : Pattern) (ha : d98522 p = 1) (hb : d120378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d98518 q = 1) (hb : d120374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d98518, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d98518, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94803 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d98519 q = 1) (hb : d120375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d98519, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d98519, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d98520 q = 1) (hb : d120376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d98520, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98520, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d98521 q = 1) (hb : d120377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d98521, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98521, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d98522 q = 1) (hb : d120378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d98522, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98522, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47060 (p : Pattern) (ha : d98528 p = 1) (hb : d121355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94833 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d98506 q = 1) (hb : d120144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d98506, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47056 q ha hb
    | true =>
      simp only [d98506, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47057 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94895 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d98507 q = 1) (hb : d120145 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d98507, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d98507, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d98508 q = 1) (hb : d121345 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d98508, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d98508, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d98509 q = 1) (hb : d121346 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d98509, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98509, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d98513 q = 1) (hb : d120335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d98513, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d98513, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47058 q ha hb
  have h8 (q : Pattern) (ha : d98514 q = 1) (hb : d121347 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d98514, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d98514, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d98515 q = 1) (hb : d121348 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d98515, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d98515, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d98516 q = 1) (hb : d121349 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d98516, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d98516, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d98517 q = 1) (hb : d121350 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d98517, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d98517, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d98523 q = 1) (hb : d120379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d98523, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d98523, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47059 q ha hb
  have h13 (q : Pattern) (ha : d98524 q = 1) (hb : d121351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d98524, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d98524, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d98525 q = 1) (hb : d121352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d98525, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d98525, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d98526 q = 1) (hb : d121353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d98526, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d98526, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d98527 q = 1) (hb : d121354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d98527, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d98527, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d98528 q = 1) (hb : d121355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d98528, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d98528, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47061 (p : Pattern) (ha : d98534 p = 1) (hb : d121361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94818 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d98529 q = 1) (hb : d121356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d98529, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d98529, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47060 q ha hb
  have h3 (q : Pattern) (ha : d98530 q = 1) (hb : d121357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d98530, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d98530, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d98531 q = 1) (hb : d121358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98531, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d98531, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d98532 q = 1) (hb : d121359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d98532, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d98532, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d98533 q = 1) (hb : d121360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d98533, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d98533, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d98534 q = 1) (hb : d121361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d98534, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98534, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47062 (p : Pattern) (ha : d196146 p = 1) (hb : d198218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194602 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194608 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d194620 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d196086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196142 q = 1) (hb : d198214 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196142, d198214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196142, d198214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d194631 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d196143 q = 1) (hb : d198215 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196143, d198215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196143, d198215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196144 q = 1) (hb : d198216 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196144, d198216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196144, d198216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d196145 q = 1) (hb : d198217 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196145, d198217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196145, d198217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d196146 q = 1) (hb : d198218 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196146, d198218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196146, d198218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47063 (p : Pattern) (ha : d196153 p = 1) (hb : d198223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d194602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194608 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d196086 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d196142 q = 1) (hb : d198214 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196142, d198214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196142, d198214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d194631 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d196143 q = 1) (hb : d198215 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196143, d198215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196143, d198215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196144 q = 1) (hb : d198216 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196144, d198216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196144, d198216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196145 q = 1) (hb : d198217 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196145, d198217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196145, d198217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d194640 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d194644 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d194646 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d196093 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d196149 q = 1) (hb : d198219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196149, d198219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d196149, d198219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d194650 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d196150 q = 1) (hb : d198220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196150, d198220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d196150, d198220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d196151 q = 1) (hb : d198221 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196151, d198221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d196151, d198221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d196152 q = 1) (hb : d198222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196152, d198222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d196152, d198222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d196153 q = 1) (hb : d198223 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196153, d198223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196153, d198223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47064 (p : Pattern) (ha : d197841 p = 1) (hb : d198230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d196093 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196149 q = 1) (hb : d198219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196149, d198219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196149, d198219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d194650 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196150 q = 1) (hb : d198220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196150, d198220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196150, d198220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d196151 q = 1) (hb : d198228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196151, d198228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196151, d198228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196152 q = 1) (hb : d198229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196152, d198229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196152, d198229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197841 q = 1) (hb : d198230 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197841, d198230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197841, d198230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47065 (p : Pattern) (ha : d197851 p = 1) (hb : d198240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d196124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d197847 q = 1) (hb : d198236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d197847, d198236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197847, d198236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d194696 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197848 q = 1) (hb : d198237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197848, d198237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197848, d198237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197849 q = 1) (hb : d198238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d197849, d198238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197849, d198238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197850 q = 1) (hb : d198239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d197850, d198239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197850, d198239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197851 q = 1) (hb : d198240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197851, d198240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197851, d198240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47066 (p : Pattern) (ha : d197857 p = 1) (hb : d198246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d194596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196154 q = 1) (hb : d198224 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d196154, d198224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47062 q ha hb
    | true =>
      simp only [d196154, d198224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47063 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196155 q = 1) (hb : d198225 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d196155, d198225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196155, d198225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197839 q = 1) (hb : d198226 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197839, d198226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197839, d198226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197840 q = 1) (hb : d198227 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197840, d198227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197840, d198227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197842 q = 1) (hb : d198231 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197842, d198231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197842, d198231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47064 q ha hb
  have h8 (q : Pattern) (ha : d197843 q = 1) (hb : d198232 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197843, d198232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d197843, d198232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d197844 q = 1) (hb : d198233 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197844, d198233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d197844, d198233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d197845 q = 1) (hb : d198234 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197845, d198234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d197845, d198234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d197846 q = 1) (hb : d198235 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197846, d198235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d197846, d198235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d197852 q = 1) (hb : d198241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197852, d198241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197852, d198241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47065 q ha hb
  have h13 (q : Pattern) (ha : d197853 q = 1) (hb : d198242 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197853, d198242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d197853, d198242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d197854 q = 1) (hb : d198243 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197854, d198243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d197854, d198243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d197855 q = 1) (hb : d198244 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197855, d198244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d197855, d198244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d197856 q = 1) (hb : d198245 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197856, d198245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d197856, d198245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d197857 q = 1) (hb : d198246 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d197857, d198246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d197857, d198246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47067 (p : Pattern) (ha : d197863 p = 1) (hb : d198252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d197858 q = 1) (hb : d198247 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d197858, d198247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197858, d198247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47066 q ha hb
  have h2 (q : Pattern) (ha : d197859 q = 1) (hb : d198248 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d197859, d198248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197859, d198248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d197860 q = 1) (hb : d198249 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d197860, d198249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197860, d198249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d197861 q = 1) (hb : d198250 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d197861, d198250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197861, d198250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d197862 q = 1) (hb : d198251 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d197862, d198251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197862, d198251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197863 q = 1) (hb : d198252 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d197863, d198252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197863, d198252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47068 (p : Pattern) (ha : d196283 p = 1) (hb : d198258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d194759 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d196278 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196279 q = 1) (hb : d198254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196279, d198254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196279, d198254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d194770 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d196280 q = 1) (hb : d198255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196280, d198255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196280, d198255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196281 q = 1) (hb : d198256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196281, d198256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196281, d198256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d196282 q = 1) (hb : d198257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196282, d198257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196282, d198257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d196283 q = 1) (hb : d198258 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196283, d198258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196283, d198258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47069 (p : Pattern) (ha : d196292 p = 1) (hb : d198263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d194741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194759 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d196278 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d196279 q = 1) (hb : d198254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196279, d198254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196279, d198254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d194770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d196280 q = 1) (hb : d198255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196280, d198255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196280, d198255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196281 q = 1) (hb : d198256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196281, d198256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196281, d198256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196282 q = 1) (hb : d198257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196282, d198257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196282, d198257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d194779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d194783 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d194785 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d196287 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d196288 q = 1) (hb : d198259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196288, d198259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d196288, d198259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d194789 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d196289 q = 1) (hb : d198260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196289, d198260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d196289, d198260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d196290 q = 1) (hb : d198261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196290, d198261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d196290, d198261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d196291 q = 1) (hb : d198262 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196291, d198262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d196291, d198262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d196292 q = 1) (hb : d198263 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196292, d198263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196292, d198263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47070 (p : Pattern) (ha : d197867 p = 1) (hb : d198270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194785 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d196287 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196288 q = 1) (hb : d198259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196288, d198259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196288, d198259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d194789 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196289 q = 1) (hb : d198260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196289, d198260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196289, d198260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d196290 q = 1) (hb : d198268 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196290, d198268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196290, d198268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196291 q = 1) (hb : d198269 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196291, d198269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196291, d198269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197867 q = 1) (hb : d198270 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197867, d198270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197867, d198270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47071 (p : Pattern) (ha : d197878 p = 1) (hb : d198280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194823 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d197873 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d197874 q = 1) (hb : d198276 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d197874, d198276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197874, d198276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d194835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197875 q = 1) (hb : d198277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197875, d198277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197875, d198277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197876 q = 1) (hb : d198278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d197876, d198278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197876, d198278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197877 q = 1) (hb : d198279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d197877, d198279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197877, d198279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197878 q = 1) (hb : d198280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197878, d198280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197878, d198280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47072 (p : Pattern) (ha : d197884 p = 1) (hb : d198286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d194735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196293 q = 1) (hb : d198264 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d196293, d198264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47068 q ha hb
    | true =>
      simp only [d196293, d198264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47069 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194796 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196294 q = 1) (hb : d198265 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d196294, d198265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196294, d198265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197865 q = 1) (hb : d198266 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197865, d198266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197865, d198266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197866 q = 1) (hb : d198267 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197866, d198267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197866, d198267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197868 q = 1) (hb : d198271 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197868, d198271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197868, d198271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47070 q ha hb
  have h8 (q : Pattern) (ha : d197869 q = 1) (hb : d198272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197869, d198272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d197869, d198272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d197870 q = 1) (hb : d198273 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197870, d198273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d197870, d198273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d197871 q = 1) (hb : d198274 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197871, d198274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d197871, d198274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d197872 q = 1) (hb : d198275 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197872, d198275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d197872, d198275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d197879 q = 1) (hb : d198281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197879, d198281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197879, d198281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47071 q ha hb
  have h13 (q : Pattern) (ha : d197880 q = 1) (hb : d198282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197880, d198282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d197880, d198282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d197881 q = 1) (hb : d198283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197881, d198283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d197881, d198283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d197882 q = 1) (hb : d198284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197882, d198284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d197882, d198284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d197883 q = 1) (hb : d198285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197883, d198285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d197883, d198285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d197884 q = 1) (hb : d198286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d197884, d198286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d197884, d198286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47073 (p : Pattern) (ha : d197890 p = 1) (hb : d198292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d197885 q = 1) (hb : d198287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d197885, d198287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197885, d198287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47072 q ha hb
  have h2 (q : Pattern) (ha : d197886 q = 1) (hb : d198288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d197886, d198288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197886, d198288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d197887 q = 1) (hb : d198289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d197887, d198289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197887, d198289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d197888 q = 1) (hb : d198290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d197888, d198290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197888, d198290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d197889 q = 1) (hb : d198291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d197889, d198291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197889, d198291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197890 q = 1) (hb : d198292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d197890, d198292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197890, d198292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47074 (p : Pattern) (ha : d196450 p = 1) (hb : d198299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194888 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d194906 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d196445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196446 q = 1) (hb : d198295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196446, d198295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196446, d198295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d194920 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d196447 q = 1) (hb : d198296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196447, d198296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196447, d198296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196448 q = 1) (hb : d198297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196448, d198297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196448, d198297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d196449 q = 1) (hb : d198298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196449, d198298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196449, d198298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d196450 q = 1) (hb : d198299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196450, d198299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196450, d198299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47075 (p : Pattern) (ha : d196460 p = 1) (hb : d198304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d194888 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194906 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d196445 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d196446 q = 1) (hb : d198295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196446, d198295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196446, d198295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d194920 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d196447 q = 1) (hb : d198296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196447, d198296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196447, d198296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196448 q = 1) (hb : d198297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196448, d198297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196448, d198297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196449 q = 1) (hb : d198298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196449, d198298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196449, d198298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d194929 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d194933 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d194935 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d196455 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d196456 q = 1) (hb : d198300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196456, d198300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d196456, d198300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d194939 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d196457 q = 1) (hb : d198301 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196457, d198301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d196457, d198301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d196458 q = 1) (hb : d198302 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196458, d198302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d196458, d198302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d196459 q = 1) (hb : d198303 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196459, d198303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d196459, d198303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d196460 q = 1) (hb : d198304 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196460, d198304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196460, d198304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47076 (p : Pattern) (ha : d197895 p = 1) (hb : d198311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d196455 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196456 q = 1) (hb : d198300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196456, d198300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196456, d198300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d194939 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196457 q = 1) (hb : d198301 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196457, d198301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196457, d198301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d196458 q = 1) (hb : d198309 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196458, d198309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196458, d198309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196459 q = 1) (hb : d198310 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196459, d198310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196459, d198310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197895 q = 1) (hb : d198311 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197895, d198311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197895, d198311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47077 (p : Pattern) (ha : d197906 p = 1) (hb : d198321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d197901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d197902 q = 1) (hb : d198317 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d197902, d198317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197902, d198317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d194995 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197903 q = 1) (hb : d198318 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197903, d198318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197903, d198318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197904 q = 1) (hb : d198319 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d197904, d198319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197904, d198319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197905 q = 1) (hb : d198320 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d197905, d198320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197905, d198320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197906 q = 1) (hb : d198321 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197906, d198321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197906, d198321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47078 (p : Pattern) (ha : d197912 p = 1) (hb : d198327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d194882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196461 q = 1) (hb : d198305 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d196461, d198305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47074 q ha hb
    | true =>
      simp only [d196461, d198305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47075 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194946 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196462 q = 1) (hb : d198306 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d196462, d198306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196462, d198306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197893 q = 1) (hb : d198307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197893, d198307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197893, d198307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197894 q = 1) (hb : d198308 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197894, d198308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197894, d198308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197896 q = 1) (hb : d198312 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197896, d198312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197896, d198312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47076 q ha hb
  have h8 (q : Pattern) (ha : d197897 q = 1) (hb : d198313 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197897, d198313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d197897, d198313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d197898 q = 1) (hb : d198314 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197898, d198314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d197898, d198314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d197899 q = 1) (hb : d198315 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197899, d198315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d197899, d198315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d197900 q = 1) (hb : d198316 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197900, d198316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d197900, d198316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d197907 q = 1) (hb : d198322 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197907, d198322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197907, d198322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47077 q ha hb
  have h13 (q : Pattern) (ha : d197908 q = 1) (hb : d198323 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197908, d198323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d197908, d198323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d197909 q = 1) (hb : d198324 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197909, d198324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d197909, d198324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d197910 q = 1) (hb : d198325 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197910, d198325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d197910, d198325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d197911 q = 1) (hb : d198326 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197911, d198326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d197911, d198326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d197912 q = 1) (hb : d198327 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d197912, d198327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d197912, d198327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47079 (p : Pattern) (ha : d197918 p = 1) (hb : d198333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d197913 q = 1) (hb : d198328 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d197913, d198328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197913, d198328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47078 q ha hb
  have h2 (q : Pattern) (ha : d197914 q = 1) (hb : d198329 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d197914, d198329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197914, d198329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d197915 q = 1) (hb : d198330 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d197915, d198330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197915, d198330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d197916 q = 1) (hb : d198331 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d197916, d198331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197916, d198331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d197917 q = 1) (hb : d198332 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d197917, d198332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197917, d198332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197918 q = 1) (hb : d198333 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d197918, d198333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197918, d198333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47080 (p : Pattern) (ha : d196676 p = 1) (hb : d198341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195049 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195055 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d195067 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d196671 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196672 q = 1) (hb : d198337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196672, d198337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196672, d198337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d195081 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d196673 q = 1) (hb : d198338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196673, d198338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196673, d198338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196674 q = 1) (hb : d198339 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196674, d198339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196674, d198339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d196675 q = 1) (hb : d198340 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196675, d198340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196675, d198340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d196676 q = 1) (hb : d198341 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196676, d198341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196676, d198341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47081 (p : Pattern) (ha : d196686 p = 1) (hb : d198346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195049 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195067 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d196671 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d196672 q = 1) (hb : d198337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196672, d198337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196672, d198337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195081 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d196673 q = 1) (hb : d198338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196673, d198338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196673, d198338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196674 q = 1) (hb : d198339 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196674, d198339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196674, d198339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196675 q = 1) (hb : d198340 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196675, d198340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196675, d198340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d195090 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d195094 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195096 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d196681 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d196682 q = 1) (hb : d198342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196682, d198342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d196682, d198342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d195100 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d196683 q = 1) (hb : d198343 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196683, d198343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d196683, d198343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d196684 q = 1) (hb : d198344 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196684, d198344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d196684, d198344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d196685 q = 1) (hb : d198345 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196685, d198345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d196685, d198345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d196686 q = 1) (hb : d198346 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196686, d198346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196686, d198346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47082 (p : Pattern) (ha : d197924 p = 1) (hb : d198353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195096 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d196681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196682 q = 1) (hb : d198342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196682, d198342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196682, d198342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195100 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196683 q = 1) (hb : d198343 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196683, d198343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196683, d198343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d196684 q = 1) (hb : d198351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196684, d198351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196684, d198351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196685 q = 1) (hb : d198352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196685, d198352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196685, d198352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197924 q = 1) (hb : d198353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197924, d198353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197924, d198353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47083 (p : Pattern) (ha : d197935 p = 1) (hb : d198363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195141 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d197930 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d197931 q = 1) (hb : d198359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d197931, d198359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197931, d198359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197932 q = 1) (hb : d198360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197932, d198360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197932, d198360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197933 q = 1) (hb : d198361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d197933, d198361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197933, d198361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197934 q = 1) (hb : d198362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d197934, d198362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197934, d198362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197935 q = 1) (hb : d198363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197935, d198363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197935, d198363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47084 (p : Pattern) (ha : d197941 p = 1) (hb : d198369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195043 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196687 q = 1) (hb : d198347 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d196687, d198347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47080 q ha hb
    | true =>
      simp only [d196687, d198347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47081 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195107 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196688 q = 1) (hb : d198348 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d196688, d198348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196688, d198348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197922 q = 1) (hb : d198349 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197922, d198349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197922, d198349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197923 q = 1) (hb : d198350 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197923, d198350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197923, d198350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197925 q = 1) (hb : d198354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197925, d198354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197925, d198354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47082 q ha hb
  have h8 (q : Pattern) (ha : d197926 q = 1) (hb : d198355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197926, d198355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d197926, d198355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d197927 q = 1) (hb : d198356 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197927, d198356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d197927, d198356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d197928 q = 1) (hb : d198357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197928, d198357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d197928, d198357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d197929 q = 1) (hb : d198358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197929, d198358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d197929, d198358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d197936 q = 1) (hb : d198364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197936, d198364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197936, d198364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47083 q ha hb
  have h13 (q : Pattern) (ha : d197937 q = 1) (hb : d198365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197937, d198365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d197937, d198365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d197938 q = 1) (hb : d198366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197938, d198366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d197938, d198366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d197939 q = 1) (hb : d198367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197939, d198367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d197939, d198367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d197940 q = 1) (hb : d198368 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197940, d198368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d197940, d198368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d197941 q = 1) (hb : d198369 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d197941, d198369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d197941, d198369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47085 (p : Pattern) (ha : d197947 p = 1) (hb : d198375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d197942 q = 1) (hb : d198370 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d197942, d198370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197942, d198370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47084 q ha hb
  have h2 (q : Pattern) (ha : d197943 q = 1) (hb : d198371 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d197943, d198371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197943, d198371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d197944 q = 1) (hb : d198372 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d197944, d198372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197944, d198372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d197945 q = 1) (hb : d198373 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d197945, d198373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197945, d198373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d197946 q = 1) (hb : d198374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d197946, d198374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197946, d198374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197947 q = 1) (hb : d198375 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d197947, d198375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197947, d198375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47086 (p : Pattern) (ha : d196903 p = 1) (hb : d198384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195211 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195217 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d195229 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d196898 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196899 q = 1) (hb : d198380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196899, d198380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196899, d198380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d195243 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d196900 q = 1) (hb : d198381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196900, d198381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196900, d198381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196901 q = 1) (hb : d198382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196901, d198382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196901, d198382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d196902 q = 1) (hb : d198383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196902, d198383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196902, d198383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d196903 q = 1) (hb : d198384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196903, d198384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196903, d198384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47087 (p : Pattern) (ha : d196913 p = 1) (hb : d198389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195211 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195217 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195229 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d196898 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d196899 q = 1) (hb : d198380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196899, d198380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196899, d198380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d195243 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d196900 q = 1) (hb : d198381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196900, d198381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196900, d198381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196901 q = 1) (hb : d198382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196901, d198382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196901, d198382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196902 q = 1) (hb : d198383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196902, d198383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196902, d198383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d195252 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d195256 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195258 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d196908 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d196909 q = 1) (hb : d198385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196909, d198385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d196909, d198385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d195262 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d196910 q = 1) (hb : d198386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196910, d198386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d196910, d198386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d196911 q = 1) (hb : d198387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196911, d198387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d196911, d198387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d196912 q = 1) (hb : d198388 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196912, d198388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d196912, d198388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d196913 q = 1) (hb : d198389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196913, d198389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196913, d198389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47088 (p : Pattern) (ha : d197954 p = 1) (hb : d198396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d196908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196909 q = 1) (hb : d198385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196909, d198385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196909, d198385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195262 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d196910 q = 1) (hb : d198386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196910, d198386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196910, d198386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d196911 q = 1) (hb : d198394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196911, d198394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196911, d198394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196912 q = 1) (hb : d198395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196912, d198395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196912, d198395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197954 q = 1) (hb : d198396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197954, d198396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197954, d198396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47089 (p : Pattern) (ha : d197965 p = 1) (hb : d198406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d195303 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d197960 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d197961 q = 1) (hb : d198402 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d197961, d198402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197961, d198402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195318 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197962 q = 1) (hb : d198403 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197962, d198403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197962, d198403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197963 q = 1) (hb : d198404 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d197963, d198404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197963, d198404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197964 q = 1) (hb : d198405 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d197964, d198405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197964, d198405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197965 q = 1) (hb : d198406 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d197965, d198406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197965, d198406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47090 (p : Pattern) (ha : d197971 p = 1) (hb : d198412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d195205 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196914 q = 1) (hb : d198390 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d196914, d198390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47086 q ha hb
    | true =>
      simp only [d196914, d198390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47087 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195269 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196915 q = 1) (hb : d198391 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d196915, d198391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196915, d198391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d197952 q = 1) (hb : d198392 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197952, d198392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197952, d198392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197953 q = 1) (hb : d198393 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197953, d198393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197953, d198393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197955 q = 1) (hb : d198397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197955, d198397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197955, d198397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47088 q ha hb
  have h8 (q : Pattern) (ha : d197956 q = 1) (hb : d198398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197956, d198398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d197956, d198398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d197957 q = 1) (hb : d198399 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197957, d198399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d197957, d198399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d197958 q = 1) (hb : d198400 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197958, d198400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d197958, d198400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d197959 q = 1) (hb : d198401 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197959, d198401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d197959, d198401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d197966 q = 1) (hb : d198407 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d197966, d198407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197966, d198407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47089 q ha hb
  have h13 (q : Pattern) (ha : d197967 q = 1) (hb : d198408 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d197967, d198408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d197967, d198408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d197968 q = 1) (hb : d198409 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d197968, d198409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d197968, d198409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d197969 q = 1) (hb : d198410 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d197969, d198410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d197969, d198410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d197970 q = 1) (hb : d198411 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d197970, d198411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d197970, d198411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d197971 q = 1) (hb : d198412 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d197971, d198412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d197971, d198412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47091 (p : Pattern) (ha : d197977 p = 1) (hb : d198418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d197972 q = 1) (hb : d198413 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d197972, d198413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197972, d198413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47090 q ha hb
  have h2 (q : Pattern) (ha : d197973 q = 1) (hb : d198414 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d197973, d198414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197973, d198414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d197974 q = 1) (hb : d198415 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d197974, d198415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197974, d198415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d197975 q = 1) (hb : d198416 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d197975, d198416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197975, d198416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d197976 q = 1) (hb : d198417 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d197976, d198417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197976, d198417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197977 q = 1) (hb : d198418 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d197977, d198418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197977, d198418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47092 (p : Pattern) (ha : d197983 p = 1) (hb : d198424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d197864 q = 1) (hb : d198253 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d197864, d198253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47061 q hb ha
    | true =>
      simp only [d197864, d198253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47067 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d197891 q = 1) (hb : d198293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d197891, d198293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197891, d198293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47073 q ha hb
  have h3 (q : Pattern) (ha : d197892 q = 1) (hb : d198294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d197892, d198294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197892, d198294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d197919 q = 1) (hb : d198334 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d197919, d198334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197919, d198334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47079 q ha hb
  have h5 (q : Pattern) (ha : d197920 q = 1) (hb : d198335 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d197920, d198335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197920, d198335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d197921 q = 1) (hb : d198336 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d197921, d198336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197921, d198336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d197948 q = 1) (hb : d198376 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d197948, d198376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197948, d198376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47085 q ha hb
  have h8 (q : Pattern) (ha : d197949 q = 1) (hb : d198377 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d197949, d198377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197949, d198377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d197950 q = 1) (hb : d198378 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d197950, d198378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197950, d198378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d197951 q = 1) (hb : d198379 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d197951, d198379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d197951, d198379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d197978 q = 1) (hb : d198419 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d197978, d198419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197978, d198419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47091 q ha hb
  have h12 (q : Pattern) (ha : d197979 q = 1) (hb : d198420 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d197979, d198420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197979, d198420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d197980 q = 1) (hb : d198421 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d197980, d198421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197980, d198421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d197981 q = 1) (hb : d198422 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d197981, d198422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197981, d198422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d197982 q = 1) (hb : d198423 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d197982, d198423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d197982, d198423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d197983 q = 1) (hb : d198424 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d197983, d198424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d197983, d198424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro47093 (p : Pattern) (ha : d197989 p = 1) (hb : d198430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d197984 q = 1) (hb : d198425 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d197984, d198425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47092 q ha hb
    | true =>
      simp only [d197984, d198425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d197985 q = 1) (hb : d198426 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d197985, d198426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197985, d198426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d197986 q = 1) (hb : d198427 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d197986, d198427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d197986, d198427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d197987 q = 1) (hb : d198428 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d197987, d198428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197987, d198428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d197988 q = 1) (hb : d198429 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d197988, d198429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197988, d198429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d197989 q = 1) (hb : d198430 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d197989, d198430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d197989, d198430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47094 (p : Pattern) (ha : d197995 p = 1) (hb : d198436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d197990 q = 1) (hb : d198431 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d197990, d198431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47093 q ha hb
    | true =>
      simp only [d197990, d198431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d197991 q = 1) (hb : d198432 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d197991, d198432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197991, d198432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d197992 q = 1) (hb : d198433 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d197992, d198433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d197992, d198433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d197993 q = 1) (hb : d198434 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d197993, d198434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197993, d198434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d197994 q = 1) (hb : d198435 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d197994, d198435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d197994, d198435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d197995 q = 1) (hb : d198436 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d197995, d198436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d197995, d198436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47095 (p : Pattern) (ha : d198001 p = 1) (hb : d198442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d197996 q = 1) (hb : d198437 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d197996, d198437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47094 q ha hb
    | true =>
      simp only [d197996, d198437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d197997 q = 1) (hb : d198438 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d197997, d198438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d197997, d198438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d197998 q = 1) (hb : d198439 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d197998, d198439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d197998, d198439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d197999 q = 1) (hb : d198440 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d197999, d198440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197999, d198440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198000 q = 1) (hb : d198441 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d198000, d198441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198000, d198441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d198001 q = 1) (hb : d198442 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d198001, d198442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198001, d198442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47096 (p : Pattern) (ha : d198007 p = 1) (hb : d198448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198002 q = 1) (hb : d198443 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d198002, d198443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47095 q ha hb
    | true =>
      simp only [d198002, d198443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d198003 q = 1) (hb : d198444 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d198003, d198444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198003, d198444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198004 q = 1) (hb : d198445 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d198004, d198445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d198004, d198445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d198005 q = 1) (hb : d198446 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d198005, d198446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198005, d198446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198006 q = 1) (hb : d198447 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d198006, d198447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198006, d198447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d198007 q = 1) (hb : d198448 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d198007, d198448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198007, d198448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47097 (p : Pattern) (ha : d198013 p = 1) (hb : d198454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198008 q = 1) (hb : d198449 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d198008, d198449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47096 q ha hb
    | true =>
      simp only [d198008, d198449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d198009 q = 1) (hb : d198450 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d198009, d198450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198009, d198450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198010 q = 1) (hb : d198451 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d198010, d198451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d198010, d198451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d198011 q = 1) (hb : d198452 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d198011, d198452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198011, d198452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198012 q = 1) (hb : d198453 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d198012, d198453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198012, d198453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d198013 q = 1) (hb : d198454 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d198013, d198454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198013, d198454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47098 (p : Pattern) (ha : d198019 p = 1) (hb : d198460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198014 q = 1) (hb : d198455 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d198014, d198455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47097 q ha hb
    | true =>
      simp only [d198014, d198455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d198015 q = 1) (hb : d198456 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d198015, d198456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198015, d198456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198016 q = 1) (hb : d198457 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d198016, d198457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d198016, d198457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d198017 q = 1) (hb : d198458 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d198017, d198458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198017, d198458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198018 q = 1) (hb : d198459 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d198018, d198459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198018, d198459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d198019 q = 1) (hb : d198460 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d198019, d198460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198019, d198460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47099 (p : Pattern) (ha : d198025 p = 1) (hb : d198466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198020 q = 1) (hb : d198461 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d198020, d198461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47098 q ha hb
    | true =>
      simp only [d198020, d198461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d198021 q = 1) (hb : d198462 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d198021, d198462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198021, d198462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198022 q = 1) (hb : d198463 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d198022, d198463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d198022, d198463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d198023 q = 1) (hb : d198464 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d198023, d198464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198023, d198464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198024 q = 1) (hb : d198465 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d198024, d198465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198024, d198465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d198025 q = 1) (hb : d198466 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d198025, d198466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198025, d198466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47100 (p : Pattern) (ha : d750 p = 1) (hb : d198467 p = 1) : d25690 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d152852 q = 1) : d21 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136 q = 1) (hb : d152852 q = 1) : d25102 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137 q = 1) (hb : d152852 q = 1) : d25103 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d750 q = 1) (hb : d198467 q = 1) : d25690 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d198467, d25690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d750, d198467, d25690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47101 (p : Pattern) (ha : d20893 p = 1) (hb : d198467 p = 1) : d200251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20892 q = 1) (hb : d198467 q = 1) : d200250 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20892, d200250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20892, d200250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d198467 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20893 q = 1) (hb : d198467 q = 1) : d200251 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20893, d200251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20893, d200251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47102 (p : Pattern) (ha : d20899 p = 1) (hb : d198467 p = 1) : d200257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47101 q ha hb
    | true =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d198467 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20897 q = 1) (hb : d198467 q = 1) : d200255 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20897, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d198467 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20898 q = 1) (hb : d198467 q = 1) : d200256 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20898, d200256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20898, d200256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20899 q = 1) (hb : d198467 q = 1) : d200257 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20899, d200257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20899, d200257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro47103 (p : Pattern) (ha : d20905 p = 1) (hb : d198467 p = 1) : d200263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d198467 q = 1) : d200262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20905 q = 1) (hb : d198467 q = 1) : d200263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20905, d200263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20905, d200263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47104 (p : Pattern) (ha : d150001 p = 1) (hb : d198467 p = 1) : d200269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d198467 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d198467 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20906 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47103 q ha hb
    | true =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d149997 q = 1) (hb : d198467 q = 1) : d200265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149997, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d198467 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149998 q = 1) (hb : d198467 q = 1) : d200266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149999 q = 1) (hb : d198467 q = 1) : d200267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149999, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150000 q = 1) (hb : d198467 q = 1) : d200268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150000, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150001 q = 1) (hb : d198467 q = 1) : d200269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150001, d200269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150001, d200269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47105 (p : Pattern) (ha : d20912 p = 1) (hb : d198467 p = 1) : d200270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d198467 q = 1) : d200262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20912 q = 1) (hb : d198467 q = 1) : d200270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20912, d200270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20912, d200270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro47106 (p : Pattern) (ha : d150006 p = 1) (hb : d198467 p = 1) : d200276 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d198467 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d198467 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20906 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47103 q ha hb
    | true =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149997 q = 1) (hb : d198467 q = 1) : d200265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149997, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d198467 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149998 q = 1) (hb : d198467 q = 1) : d200266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149999 q = 1) (hb : d198467 q = 1) : d200267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149999, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150000 q = 1) (hb : d198467 q = 1) : d200268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150000, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d198467 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d198467 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20913 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47105 q ha hb
    | true =>
      simp only [d20913, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150002 q = 1) (hb : d198467 q = 1) : d200272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150002, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d198467 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d150003 q = 1) (hb : d198467 q = 1) : d200273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150003, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150004 q = 1) (hb : d198467 q = 1) : d200274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150004, d200274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150004, d200274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150005 q = 1) (hb : d198467 q = 1) : d200275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150005, d200275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150005, d200275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d150006 q = 1) (hb : d198467 q = 1) : d200276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150006, d200276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150006, d200276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47107 (p : Pattern) (ha : d150013 p = 1) (hb : d198467 p = 1) : d200283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47105 q ha hb
    | true =>
      simp only [d20913, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150002 q = 1) (hb : d198467 q = 1) : d200272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150002, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d198467 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150003 q = 1) (hb : d198467 q = 1) : d200273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150003, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150011 q = 1) (hb : d198467 q = 1) : d200281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150011, d200281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150011, d200281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150012 q = 1) (hb : d198467 q = 1) : d200282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150012, d200282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150012, d200282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150013 q = 1) (hb : d198467 q = 1) : d200283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150013, d200283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150013, d200283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47108 (p : Pattern) (ha : d20932 p = 1) (hb : d198467 p = 1) : d200290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20931 q = 1) (hb : d198467 q = 1) : d200289 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20931, d200289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20931, d200289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d198467 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20932 q = 1) (hb : d198467 q = 1) : d200290 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20932, d200290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20932, d200290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47109 (p : Pattern) (ha : d20938 p = 1) (hb : d198467 p = 1) : d200296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47108 q ha hb
    | true =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d198467 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20936 q = 1) (hb : d198467 q = 1) : d200294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20936, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d198467 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20937 q = 1) (hb : d198467 q = 1) : d200295 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20937, d200295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20937, d200295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20938 q = 1) (hb : d198467 q = 1) : d200296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20938, d200296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20938, d200296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro47110 (p : Pattern) (ha : d20944 p = 1) (hb : d198467 p = 1) : d200302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47109 q ha hb
    | true =>
      simp only [d20939, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d198467 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20941 q = 1) (hb : d198467 q = 1) : d200299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20941, d200299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20941, d200299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20942 q = 1) (hb : d198467 q = 1) : d200300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20942, d200300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20942, d200300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20943 q = 1) (hb : d198467 q = 1) : d200301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20943, d200301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20943, d200301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20944 q = 1) (hb : d198467 q = 1) : d200302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20944, d200302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20944, d200302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro47111 (p : Pattern) (ha : d150023 p = 1) (hb : d198467 p = 1) : d200308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d198467 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d198467 q = 1) : d200303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47110 q ha hb
    | true =>
      simp only [d20945, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150019 q = 1) (hb : d198467 q = 1) : d200304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150019, d200304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150019, d200304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d198467 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150020 q = 1) (hb : d198467 q = 1) : d200305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150020, d200305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150020, d200305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150021 q = 1) (hb : d198467 q = 1) : d200306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150021, d200306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150021, d200306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150022 q = 1) (hb : d198467 q = 1) : d200307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150022, d200307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150022, d200307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150023 q = 1) (hb : d198467 q = 1) : d200308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150023, d200308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150023, d200308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47112 (p : Pattern) (ha : d150029 p = 1) (hb : d198467 p = 1) : d200314 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d198467 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150007 q = 1) (hb : d198467 q = 1) : d200277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150007, d200277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47104 q ha hb
    | true =>
      simp only [d150007, d200277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47106 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d198467 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150008 q = 1) (hb : d198467 q = 1) : d200278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150008, d200278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150008, d200278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150009 q = 1) (hb : d198467 q = 1) : d200279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150009, d200279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150009, d200279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150010 q = 1) (hb : d198467 q = 1) : d200280 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150010, d200280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150010, d200280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150014 q = 1) (hb : d198467 q = 1) : d200284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150014, d200284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150014, d200284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47107 q ha hb
  have h8 (q : Pattern) (ha : d150015 q = 1) (hb : d198467 q = 1) : d200285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150015, d200285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150015, d200285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d150016 q = 1) (hb : d198467 q = 1) : d200286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150016, d200286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150016, d200286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d150017 q = 1) (hb : d198467 q = 1) : d200287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150017, d200287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150017, d200287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150018 q = 1) (hb : d198467 q = 1) : d200288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150018, d200288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150018, d200288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150024 q = 1) (hb : d198467 q = 1) : d200309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150024, d200309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150024, d200309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47111 q ha hb
  have h13 (q : Pattern) (ha : d150025 q = 1) (hb : d198467 q = 1) : d200310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150025, d200310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150025, d200310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d150026 q = 1) (hb : d198467 q = 1) : d200311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150026, d200311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150026, d200311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d150027 q = 1) (hb : d198467 q = 1) : d200312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150027, d200312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150027, d200312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d150028 q = 1) (hb : d198467 q = 1) : d200313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150028, d200313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150028, d200313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150029 q = 1) (hb : d198467 q = 1) : d200314 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150029, d200314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150029, d200314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47113 (p : Pattern) (ha : d20966 p = 1) (hb : d198467 p = 1) : d200324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47103 q ha hb
    | true =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20966 q = 1) (hb : d198467 q = 1) : d200324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47114 (p : Pattern) (ha : d20973 p = 1) (hb : d198467 p = 1) : d200331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47103 q ha hb
    | true =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20913 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47105 q ha hb
    | true =>
      simp only [d20913, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20969 q = 1) (hb : d198467 q = 1) : d200327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20970 q = 1) (hb : d198467 q = 1) : d200328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20970, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20971 q = 1) (hb : d198467 q = 1) : d200329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20972 q = 1) (hb : d198467 q = 1) : d200330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20973 q = 1) (hb : d198467 q = 1) : d200331 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20973, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro47115 (p : Pattern) (ha : d21058 p = 1) (hb : d198467 p = 1) : d200404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47103 q ha hb
    | true =>
      simp only [d20906, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d198467 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21058 q = 1) (hb : d198467 q = 1) : d200404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21058, d200404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21058, d200404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47116 (p : Pattern) (ha : d20978 p = 1) (hb : d198467 p = 1) : d200336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d198467 q = 1) : d200335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20978 q = 1) (hb : d198467 q = 1) : d200336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20978, d200336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20978, d200336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47117 (p : Pattern) (ha : d20985 p = 1) (hb : d198467 p = 1) : d200343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d198467 q = 1) : d200341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d198467 q = 1) : d200342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20985 q = 1) (hb : d198467 q = 1) : d200343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20985, d200343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20985, d200343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47118 (p : Pattern) (ha : d5450 p = 1) (hb : d198467 p = 1) : d200353 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5448 q = 1) (hb : d152852 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5448, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5449 q = 1) (hb : d152852 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5450 q = 1) (hb : d198467 q = 1) : d200353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5450, d198467, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5450, d198467, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47119 (p : Pattern) (ha : d20989 p = 1) (hb : d198467 p = 1) : d200347 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d314 q = 1) : d314 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d316 q = 1) (hb : d152852 q = 1) : d25211 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d25211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316, d25211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d317 q = 1) (hb : d152852 q = 1) : d25212 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d317, d25212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20989 q = 1) (hb : d198467 q = 1) : d200347 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d20989, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20989, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47120 (p : Pattern) (ha : d20996 p = 1) (hb : d198467 p = 1) : d200359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
    | true =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d198467 q = 1) : d200352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5451 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5453 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5454 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20995 q = 1) (hb : d198467 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20995, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d20996 q = 1) (hb : d198467 q = 1) : d200359 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20996, d200359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20996, d200359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro47121 (p : Pattern) (ha : d21002 p = 1) (hb : d198467 p = 1) : d200365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47120 q ha hb
    | true =>
      simp only [d20997, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47101 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20894 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47101 q ha hb
    | true =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20895 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20896 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21000 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d198467 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20897 q = 1) (hb : d198467 q = 1) : d200255 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20897, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21001 q = 1) (hb : d198467 q = 1) : d200364 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21001, d200364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21001, d200364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21002 q = 1) (hb : d198467 q = 1) : d200365 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21002, d200365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21002, d200365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro47122 (p : Pattern) (ha : d21008 p = 1) (hb : d198467 p = 1) : d200371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d198467 q = 1) : d200366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47121 q ha hb
    | true =>
      simp only [d21003, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d198467 q = 1) : d200367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d198467 q = 1) : d200368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d198467 q = 1) : d200369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d198467 q = 1) : d200370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21008 q = 1) (hb : d198467 q = 1) : d200371 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21008, d200371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21008, d200371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47123 (p : Pattern) (ha : d21029 p = 1) (hb : d198467 p = 1) : d200377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d198467 q = 1) : d200374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d198467 q = 1) : d200375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d198467 q = 1) : d200376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21029 q = 1) (hb : d198467 q = 1) : d200377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21029, d200377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21029, d200377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47124 (p : Pattern) (ha : d150039 p = 1) (hb : d198467 p = 1) : d200383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d198467 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d198467 q = 1) : d200337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47116 q ha hb
    | true =>
      simp only [d20979, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d198467 q = 1) : d200338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d198467 q = 1) : d200339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d198467 q = 1) : d200340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d198467 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d198467 q = 1) : d200344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47117 q ha hb
    | true =>
      simp only [d20986, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d198467 q = 1) : d200345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d198467 q = 1) : d200346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d198467 q = 1) : d200372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47122 q ha hb
    | true =>
      simp only [d21009, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47103 q ha hb
  have h11 (q : Pattern) (ha : d150035 q = 1) (hb : d198467 q = 1) : d200373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150035, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d198467 q = 1) : d200378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47123 q ha hb
    | true =>
      simp only [d21030, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d198467 q = 1) : d200379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150036 q = 1) (hb : d198467 q = 1) : d200380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150037 q = 1) (hb : d198467 q = 1) : d200381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150037, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150038 q = 1) (hb : d198467 q = 1) : d200382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150038, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150039 q = 1) (hb : d198467 q = 1) : d200383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d200383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150039, d200383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47125 (p : Pattern) (ha : d21036 p = 1) (hb : d198467 p = 1) : d200384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d198467 q = 1) : d200335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21036 q = 1) (hb : d198467 q = 1) : d200384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21036, d200384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21036, d200384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro47126 (p : Pattern) (ha : d21041 p = 1) (hb : d198467 p = 1) : d200389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d198467 q = 1) : d200341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d198467 q = 1) : d200342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21041 q = 1) (hb : d198467 q = 1) : d200389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21041, d200389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21041, d200389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro47127 (p : Pattern) (ha : d21045 p = 1) (hb : d198467 p = 1) : d200393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d198467 q = 1) : d200366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47121 q ha hb
    | true =>
      simp only [d21003, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d198467 q = 1) : d200367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d198467 q = 1) : d200368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d198467 q = 1) : d200369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d198467 q = 1) : d200370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21045 q = 1) (hb : d198467 q = 1) : d200393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21045, d200393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21045, d200393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47128 (p : Pattern) (ha : d21050 p = 1) (hb : d198467 p = 1) : d200396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47102 q ha hb
    | true =>
      simp only [d20900, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d198467 q = 1) : d200374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d198467 q = 1) : d200375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d198467 q = 1) : d200376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21050 q = 1) (hb : d198467 q = 1) : d200396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21050, d200396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21050, d200396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47129 (p : Pattern) (ha : d150044 p = 1) (hb : d198467 p = 1) : d200402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d198467 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d198467 q = 1) : d200337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47116 q ha hb
    | true =>
      simp only [d20979, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d198467 q = 1) : d200338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d198467 q = 1) : d200339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d198467 q = 1) : d200340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d198467 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d198467 q = 1) : d200344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47117 q ha hb
    | true =>
      simp only [d20986, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d198467 q = 1) : d200345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d198467 q = 1) : d200346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d198467 q = 1) : d200372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47122 q ha hb
    | true =>
      simp only [d21009, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47103 q ha hb
  have h11 (q : Pattern) (ha : d150035 q = 1) (hb : d198467 q = 1) : d200373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150035, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d198467 q = 1) : d200378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47123 q ha hb
    | true =>
      simp only [d21030, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d198467 q = 1) : d200379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150036 q = 1) (hb : d198467 q = 1) : d200380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150037 q = 1) (hb : d198467 q = 1) : d200381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150037, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150038 q = 1) (hb : d198467 q = 1) : d200382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150038, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d198467 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d21037 q = 1) (hb : d198467 q = 1) : d200385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21037, d200385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47125 q ha hb
    | true =>
      simp only [d21037, d200385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21038 q = 1) (hb : d198467 q = 1) : d200386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21038, d200386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21038, d200386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21039 q = 1) (hb : d198467 q = 1) : d200387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21039, d200387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21039, d200387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d21040 q = 1) (hb : d198467 q = 1) : d200388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21040, d200388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21040, d200388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d198467 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d21042 q = 1) (hb : d198467 q = 1) : d200390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21042, d200390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47126 q ha hb
    | true =>
      simp only [d21042, d200390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d21043 q = 1) (hb : d198467 q = 1) : d200391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21043, d200391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21043, d200391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d21044 q = 1) (hb : d198467 q = 1) : d200392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21044, d200392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21044, d200392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21046 q = 1) (hb : d198467 q = 1) : d200394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47127 q ha hb
    | true =>
      simp only [d21046, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47105 q ha hb
  have h27 (q : Pattern) (ha : d150040 q = 1) (hb : d198467 q = 1) : d200395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d150040, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d21051 q = 1) (hb : d198467 q = 1) : d200397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47128 q ha hb
    | true =>
      simp only [d21051, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d21052 q = 1) (hb : d198467 q = 1) : d200398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d21052, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d150041 q = 1) (hb : d198467 q = 1) : d200399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d150041, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d150042 q = 1) (hb : d198467 q = 1) : d200400 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d200400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d150042, d200400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d150043 q = 1) (hb : d198467 q = 1) : d200401 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d200401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150043, d200401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d150044 q = 1) (hb : d198467 q = 1) : d200402 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d200402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150044, d200402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro47130 (p : Pattern) (ha : d150051 p = 1) (hb : d198467 p = 1) : d200411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21046 q = 1) (hb : d198467 q = 1) : d200394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47127 q ha hb
    | true =>
      simp only [d21046, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47105 q ha hb
  have h2 (q : Pattern) (ha : d150040 q = 1) (hb : d198467 q = 1) : d200395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150040, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21051 q = 1) (hb : d198467 q = 1) : d200397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47128 q ha hb
    | true =>
      simp only [d21051, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21052 q = 1) (hb : d198467 q = 1) : d200398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21052, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150041 q = 1) (hb : d198467 q = 1) : d200399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150041, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150049 q = 1) (hb : d198467 q = 1) : d200409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d200409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150049, d200409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150050 q = 1) (hb : d198467 q = 1) : d200410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d200410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150050, d200410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150051 q = 1) (hb : d198467 q = 1) : d200411 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d200411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150051, d200411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47131 (p : Pattern) (ha : d21077 p = 1) (hb : d198467 p = 1) : d200427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
    | true =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d198467 q = 1) : d200421 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5495 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
  have h15 (q : Pattern) (ha : d5451 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5496 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5452 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5497 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5498 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d21076 q = 1) (hb : d198467 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21076, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d21077 q = 1) (hb : d198467 q = 1) : d200427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21077, d200427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21077, d200427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro47132 (p : Pattern) (ha : d21083 p = 1) (hb : d198467 p = 1) : d200433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47131 q ha hb
    | true =>
      simp only [d21078, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47108 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20933 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47108 q ha hb
    | true =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20934 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20935 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21081 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d198467 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20936 q = 1) (hb : d198467 q = 1) : d200294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20936, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21082 q = 1) (hb : d198467 q = 1) : d200432 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21082, d200432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21082, d200432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21083 q = 1) (hb : d198467 q = 1) : d200433 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21083, d200433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21083, d200433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro47133 (p : Pattern) (ha : d21089 p = 1) (hb : d198467 p = 1) : d200439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21084 q = 1) (hb : d198467 q = 1) : d200434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21084, d200434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47132 q ha hb
    | true =>
      simp only [d21084, d200434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21085 q = 1) (hb : d198467 q = 1) : d200435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21085, d200435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21085, d200435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20939 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47109 q ha hb
    | true =>
      simp only [d20939, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20940 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21086 q = 1) (hb : d198467 q = 1) : d200436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21086, d200436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21086, d200436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21087 q = 1) (hb : d198467 q = 1) : d200437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21087, d200437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21087, d200437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21088 q = 1) (hb : d198467 q = 1) : d200438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21088, d200438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21088, d200438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21089 q = 1) (hb : d198467 q = 1) : d200439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21089, d200439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21089, d200439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47134 (p : Pattern) (ha : d21110 p = 1) (hb : d198467 p = 1) : d200445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47109 q ha hb
    | true =>
      simp only [d20939, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21107 q = 1) (hb : d198467 q = 1) : d200442 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21107, d200442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21107, d200442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21108 q = 1) (hb : d198467 q = 1) : d200443 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21108, d200443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21108, d200443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21109 q = 1) (hb : d198467 q = 1) : d200444 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21109, d200444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21109, d200444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21110 q = 1) (hb : d198467 q = 1) : d200445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21110, d200445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21110, d200445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47135 (p : Pattern) (ha : d150061 p = 1) (hb : d198467 p = 1) : d200451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21090 q = 1) (hb : d198467 q = 1) : d200440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21090, d200440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47133 q ha hb
    | true =>
      simp only [d21090, d200440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47110 q ha hb
  have h2 (q : Pattern) (ha : d150057 q = 1) (hb : d198467 q = 1) : d200441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d200441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150057, d200441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21111 q = 1) (hb : d198467 q = 1) : d200446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21111, d200446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47134 q ha hb
    | true =>
      simp only [d21111, d200446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21112 q = 1) (hb : d198467 q = 1) : d200447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21112, d200447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21112, d200447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150058 q = 1) (hb : d198467 q = 1) : d200448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d200448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150058, d200448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150059 q = 1) (hb : d198467 q = 1) : d200449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d200449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150059, d200449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150060 q = 1) (hb : d198467 q = 1) : d200450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d200450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150060, d200450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150061 q = 1) (hb : d198467 q = 1) : d200451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d200451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150061, d200451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47136 (p : Pattern) (ha : d150067 p = 1) (hb : d198467 p = 1) : d200457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20967 q = 1) (hb : d198467 q = 1) : d200325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20967, d200325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20967, d200325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47113 q ha hb
  have h2 (q : Pattern) (ha : d20968 q = 1) (hb : d198467 q = 1) : d200326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20968, d200326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20968, d200326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20974 q = 1) (hb : d198467 q = 1) : d200332 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47113 q ha hb
    | true =>
      simp only [d20974, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47114 q ha hb
  have h4 (q : Pattern) (ha : d20975 q = 1) (hb : d198467 q = 1) : d200333 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20975, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20976 q = 1) (hb : d198467 q = 1) : d200334 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20976, d200334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20976, d200334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150045 q = 1) (hb : d198467 q = 1) : d200403 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d200403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47124 q ha hb
    | true =>
      simp only [d150045, d200403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47129 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d198467 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21059 q = 1) (hb : d198467 q = 1) : d200405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21059, d200405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47115 q ha hb
    | true =>
      simp only [d21059, d200405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150046 q = 1) (hb : d198467 q = 1) : d200406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d200406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150046, d200406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150047 q = 1) (hb : d198467 q = 1) : d200407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d200407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150047, d200407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d150048 q = 1) (hb : d198467 q = 1) : d200408 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d200408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150048, d200408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150052 q = 1) (hb : d198467 q = 1) : d200412 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d200412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150052, d200412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47130 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d198467 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d150053 q = 1) (hb : d198467 q = 1) : d200413 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d200413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150053, d200413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150054 q = 1) (hb : d198467 q = 1) : d200414 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d200414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150054, d200414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150055 q = 1) (hb : d198467 q = 1) : d200415 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d200415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150055, d200415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d150056 q = 1) (hb : d198467 q = 1) : d200416 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d200416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150056, d200416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150062 q = 1) (hb : d198467 q = 1) : d200452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d200452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150062, d200452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47135 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d198467 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d150063 q = 1) (hb : d198467 q = 1) : d200453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d200453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150063, d200453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d150064 q = 1) (hb : d198467 q = 1) : d200454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d200454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150064, d200454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150065 q = 1) (hb : d198467 q = 1) : d200455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d200455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150065, d200455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150066 q = 1) (hb : d198467 q = 1) : d200456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d200456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150066, d200456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d150067 q = 1) (hb : d198467 q = 1) : d200457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d200457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150067, d200457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro47137 (p : Pattern) (ha : d150073 p = 1) (hb : d198467 p = 1) : d200463 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d198467 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150030 q = 1) (hb : d198467 q = 1) : d200315 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150030, d200315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150030, d200315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47112 q ha hb
  have h3 (q : Pattern) (ha : d150031 q = 1) (hb : d198467 q = 1) : d200316 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150031, d200316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150031, d200316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150032 q = 1) (hb : d198467 q = 1) : d200317 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150032, d200317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150032, d200317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150033 q = 1) (hb : d198467 q = 1) : d200318 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150033, d200318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150033, d200318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150034 q = 1) (hb : d198467 q = 1) : d200319 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150034, d200319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150034, d200319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150068 q = 1) (hb : d198467 q = 1) : d200458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d200458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150068, d200458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47136 q ha hb
  have h8 (q : Pattern) (ha : d150069 q = 1) (hb : d198467 q = 1) : d200459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d200459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150069, d200459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150070 q = 1) (hb : d198467 q = 1) : d200460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d200460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150070, d200460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150071 q = 1) (hb : d198467 q = 1) : d200461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d200461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150071, d200461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150072 q = 1) (hb : d198467 q = 1) : d200462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d200462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150072, d200462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150073 q = 1) (hb : d198467 q = 1) : d200463 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d200463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150073, d200463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro47138 (p : Pattern) (ha : d21131 p = 1) (hb : d198467 p = 1) : d200466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47120 q ha hb
    | true =>
      simp only [d20997, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47101 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20894 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47101 q ha hb
    | true =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20895 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20896 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21000 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21129 q = 1) (hb : d198467 q = 1) : d200464 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21129, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21130 q = 1) (hb : d198467 q = 1) : d200465 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21130, d200465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21130, d200465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21131 q = 1) (hb : d198467 q = 1) : d200466 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21131, d200466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21131, d200466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro47139 (p : Pattern) (ha : d21135 p = 1) (hb : d198467 p = 1) : d200470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47101 q ha hb
    | true =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21129 q = 1) (hb : d198467 q = 1) : d200464 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21129, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21134 q = 1) (hb : d198467 q = 1) : d200469 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21134, d200469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21134, d200469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21135 q = 1) (hb : d198467 q = 1) : d200470 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21135, d200470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21135, d200470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro47140 (p : Pattern) (ha : d21141 p = 1) (hb : d198467 p = 1) : d200476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d198467 q = 1) : d200475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21141 q = 1) (hb : d198467 q = 1) : d200476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21141, d200476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21141, d200476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47141 (p : Pattern) (ha : d21145 p = 1) (hb : d198467 p = 1) : d200480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d198467 q = 1) : d200479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21145 q = 1) (hb : d198467 q = 1) : d200480 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21145, d200480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21145, d200480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47142 (p : Pattern) (ha : d21151 p = 1) (hb : d198467 p = 1) : d200486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47140 q ha hb
    | true =>
      simp only [d21146, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47141 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21151 q = 1) (hb : d198467 q = 1) : d200486 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21151, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21151, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47143 (p : Pattern) (ha : d21154 p = 1) (hb : d198467 p = 1) : d200489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d198467 q = 1) : d200475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21154 q = 1) (hb : d198467 q = 1) : d200489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21154, d200489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21154, d200489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47144 (p : Pattern) (ha : d21155 p = 1) (hb : d198467 p = 1) : d200490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d198467 q = 1) : d200479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21155 q = 1) (hb : d198467 q = 1) : d200490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21155, d200490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21155, d200490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47145 (p : Pattern) (ha : d21161 p = 1) (hb : d198467 p = 1) : d200496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47140 q ha hb
    | true =>
      simp only [d21146, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47141 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21156 q = 1) (hb : d198467 q = 1) : d200491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47143 q ha hb
    | true =>
      simp only [d21156, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47144 q ha hb
  have h7 (q : Pattern) (ha : d21157 q = 1) (hb : d198467 q = 1) : d200492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21158 q = 1) (hb : d198467 q = 1) : d200493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21158, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21159 q = 1) (hb : d198467 q = 1) : d200494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21160 q = 1) (hb : d198467 q = 1) : d200495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21161 q = 1) (hb : d198467 q = 1) : d200496 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21161, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21161, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47146 (p : Pattern) (ha : d21288 p = 1) (hb : d198467 p = 1) : d200585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47140 q ha hb
    | true =>
      simp only [d21146, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47141 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21283 q = 1) (hb : d198467 q = 1) : d200580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47141 q ha hb
    | true =>
      simp only [d21283, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21284 q = 1) (hb : d198467 q = 1) : d200581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21285 q = 1) (hb : d198467 q = 1) : d200582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21285, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21286 q = 1) (hb : d198467 q = 1) : d200583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21287 q = 1) (hb : d198467 q = 1) : d200584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21288 q = 1) (hb : d198467 q = 1) : d200585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21288, d200585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21288, d200585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47147 (p : Pattern) (ha : d21294 p = 1) (hb : d198467 p = 1) : d200591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21283 q = 1) (hb : d198467 q = 1) : d200580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47141 q ha hb
    | true =>
      simp only [d21283, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21284 q = 1) (hb : d198467 q = 1) : d200581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21285 q = 1) (hb : d198467 q = 1) : d200582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21285, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21286 q = 1) (hb : d198467 q = 1) : d200583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21287 q = 1) (hb : d198467 q = 1) : d200584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21289 q = 1) (hb : d198467 q = 1) : d200586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47144 q ha hb
    | true =>
      simp only [d21289, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21290 q = 1) (hb : d198467 q = 1) : d200587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21291 q = 1) (hb : d198467 q = 1) : d200588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21291, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21292 q = 1) (hb : d198467 q = 1) : d200589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21293 q = 1) (hb : d198467 q = 1) : d200590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21294 q = 1) (hb : d198467 q = 1) : d200591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21294, d200591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21294, d200591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47148 (p : Pattern) (ha : d21303 p = 1) (hb : d198467 p = 1) : d200600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21289 q = 1) (hb : d198467 q = 1) : d200586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47144 q ha hb
    | true =>
      simp only [d21289, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21290 q = 1) (hb : d198467 q = 1) : d200587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21291 q = 1) (hb : d198467 q = 1) : d200588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21291, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21292 q = 1) (hb : d198467 q = 1) : d200589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21293 q = 1) (hb : d198467 q = 1) : d200590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21303 q = 1) (hb : d198467 q = 1) : d200600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21303, d200600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21303, d200600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47149 (p : Pattern) (ha : d21342 p = 1) (hb : d198467 p = 1) : d200639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47108 q ha hb
    | true =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21332 q = 1) (hb : d198467 q = 1) : d200629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21332, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21341 q = 1) (hb : d198467 q = 1) : d200638 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21341, d200638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21341, d200638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21342 q = 1) (hb : d198467 q = 1) : d200639 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21342, d200639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21342, d200639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro47150 (p : Pattern) (ha : d21398 p = 1) (hb : d198467 p = 1) : d200662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21343 q = 1) (hb : d198467 q = 1) : d200640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47149 q ha hb
    | true =>
      simp only [d21343, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21344 q = 1) (hb : d198467 q = 1) : d200641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21395 q = 1) (hb : d198467 q = 1) : d200659 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21395, d200659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21395, d200659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21396 q = 1) (hb : d198467 q = 1) : d200660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21396, d200660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21396, d200660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21397 q = 1) (hb : d198467 q = 1) : d200661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21397, d200661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21397, d200661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21398 q = 1) (hb : d198467 q = 1) : d200662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21398, d200662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21398, d200662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47151 (p : Pattern) (ha : d21404 p = 1) (hb : d198467 p = 1) : d200668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21399 q = 1) (hb : d198467 q = 1) : d200663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21399, d200663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47150 q ha hb
    | true =>
      simp only [d21399, d200663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21400 q = 1) (hb : d198467 q = 1) : d200664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21400, d200664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21400, d200664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21401 q = 1) (hb : d198467 q = 1) : d200665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21401, d200665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21401, d200665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21402 q = 1) (hb : d198467 q = 1) : d200666 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21402, d200666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21402, d200666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21403 q = 1) (hb : d198467 q = 1) : d200667 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21403, d200667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21403, d200667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21404 q = 1) (hb : d198467 q = 1) : d200668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21404, d200668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21404, d200668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47152 (p : Pattern) (ha : d21166 p = 1) (hb : d198467 p = 1) : d200501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d198467 q = 1) : d200500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21166 q = 1) (hb : d198467 q = 1) : d200501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21166, d200501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21166, d200501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47153 (p : Pattern) (ha : d21168 p = 1) (hb : d198467 p = 1) : d200503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d198467 q = 1) : d200502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21168 q = 1) (hb : d198467 q = 1) : d200503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21168, d200503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21168, d200503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47154 (p : Pattern) (ha : d21175 p = 1) (hb : d198467 p = 1) : d200510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d198467 q = 1) : d200508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d198467 q = 1) : d200509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21175 q = 1) (hb : d198467 q = 1) : d200510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21175, d200510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21175, d200510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47155 (p : Pattern) (ha : d21178 p = 1) (hb : d198467 p = 1) : d200513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d198467 q = 1) : d200511 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d198467 q = 1) : d200512 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21178 q = 1) (hb : d198467 q = 1) : d200513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21178, d200513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21178, d200513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47156 (p : Pattern) (ha : d21182 p = 1) (hb : d198467 p = 1) : d200517 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d532 q = 1) : d532 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d533 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d538 q = 1) : d538 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d539 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d540 q = 1) (hb : d152852 q = 1) : d25430 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d25430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d540, d25430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d541 q = 1) (hb : d152852 q = 1) : d25431 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d25431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d541, d25431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21182 q = 1) (hb : d198467 q = 1) : d200517 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21182, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21182, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47157 (p : Pattern) (ha : d21188 p = 1) (hb : d198467 p = 1) : d200523 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d314 q = 1) : d314 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9464 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9464, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9464, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9465 q = 1) (hb : d152852 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9465, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9465, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9466 q = 1) (hb : d152852 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9466, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9466, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21188 q = 1) (hb : d198467 q = 1) : d200523 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21188, d198467, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21188, d198467, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47158 (p : Pattern) (ha : d21194 p = 1) (hb : d198467 p = 1) : d200529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
    | true =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20990 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
    | true =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20991 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20992 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20993 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20993, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21187 q = 1) (hb : d198467 q = 1) : d200522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21187, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21189 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
    | true =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21190 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21191 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21192 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21192, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5451 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d5452 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5453 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5454 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21193 q = 1) (hb : d198467 q = 1) : d200528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21193, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21193, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21194 q = 1) (hb : d198467 q = 1) : d200529 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21194, d200529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21194, d200529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47159 (p : Pattern) (ha : d21198 p = 1) (hb : d198467 p = 1) : d200533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20995 q = 1) (hb : d198467 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20995, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d198467 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21198 q = 1) (hb : d198467 q = 1) : d200533 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21198, d200533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21198, d200533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47160 (p : Pattern) (ha : d21204 p = 1) (hb : d198467 p = 1) : d200539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21195 q = 1) (hb : d198467 q = 1) : d200530 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21195, d200530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47158 q ha hb
    | true =>
      simp only [d21195, d200530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47120 q ha hb
  have h2 (q : Pattern) (ha : d21196 q = 1) (hb : d198467 q = 1) : d200531 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21196, d200531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21196, d200531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21197 q = 1) (hb : d198467 q = 1) : d200532 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21197, d200532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21197, d200532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21199 q = 1) (hb : d198467 q = 1) : d200534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21199, d200534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47120 q ha hb
    | true =>
      simp only [d21199, d200534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47159 q ha hb
  have h5 (q : Pattern) (ha : d21200 q = 1) (hb : d198467 q = 1) : d200535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21200, d200535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21200, d200535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21201 q = 1) (hb : d198467 q = 1) : d200536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21201, d200536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21201, d200536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21202 q = 1) (hb : d198467 q = 1) : d200537 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21202, d200537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21202, d200537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20997 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47120 q ha hb
    | true =>
      simp only [d20997, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47101 q ha hb
  have h9 (q : Pattern) (ha : d20998 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20999 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20894 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47101 q ha hb
    | true =>
      simp only [d20894, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20895 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20896 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21000 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21000, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21203 q = 1) (hb : d198467 q = 1) : d200538 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21203, d200538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21203, d200538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21204 q = 1) (hb : d198467 q = 1) : d200539 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21204, d200539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21204, d200539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro47161 (p : Pattern) (ha : d21210 p = 1) (hb : d198467 p = 1) : d200545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d198467 q = 1) : d200540 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47160 q ha hb
    | true =>
      simp only [d21205, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d198467 q = 1) : d200541 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d198467 q = 1) : d200542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d198467 q = 1) : d200543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d198467 q = 1) : d200544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21210 q = 1) (hb : d198467 q = 1) : d200545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21210, d200545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21210, d200545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47162 (p : Pattern) (ha : d21251 p = 1) (hb : d198467 p = 1) : d200551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d198467 q = 1) : d200548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d198467 q = 1) : d200549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d198467 q = 1) : d200550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21251 q = 1) (hb : d198467 q = 1) : d200551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21251, d200551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21251, d200551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47163 (p : Pattern) (ha : d150078 p = 1) (hb : d198467 p = 1) : d200557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d198467 q = 1) : d200504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47152 q ha hb
    | true =>
      simp only [d21169, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47153 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d198467 q = 1) : d200505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d198467 q = 1) : d200506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d198467 q = 1) : d200507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d198467 q = 1) : d200514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47154 q ha hb
    | true =>
      simp only [d21179, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47155 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d198467 q = 1) : d200515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d198467 q = 1) : d200516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d198467 q = 1) : d200546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47161 q ha hb
    | true =>
      simp only [d21211, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47140 q ha hb
  have h9 (q : Pattern) (ha : d150074 q = 1) (hb : d198467 q = 1) : d200547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150074, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d198467 q = 1) : d200552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47162 q ha hb
    | true =>
      simp only [d21252, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d198467 q = 1) : d200553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150075 q = 1) (hb : d198467 q = 1) : d200554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150076 q = 1) (hb : d198467 q = 1) : d200555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150076, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150077 q = 1) (hb : d198467 q = 1) : d200556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150077, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150078 q = 1) (hb : d198467 q = 1) : d200557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d200557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150078, d200557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47164 (p : Pattern) (ha : d21258 p = 1) (hb : d198467 p = 1) : d200558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d198467 q = 1) : d200500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21258 q = 1) (hb : d198467 q = 1) : d200558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21258, d200558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21258, d200558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47165 (p : Pattern) (ha : d21259 p = 1) (hb : d198467 p = 1) : d200559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d198467 q = 1) : d200502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21259 q = 1) (hb : d198467 q = 1) : d200559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21259, d200559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21259, d200559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47166 (p : Pattern) (ha : d21264 p = 1) (hb : d198467 p = 1) : d200564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d198467 q = 1) : d200508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d198467 q = 1) : d200509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21264 q = 1) (hb : d198467 q = 1) : d200564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21264, d200564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21264, d200564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47167 (p : Pattern) (ha : d21265 p = 1) (hb : d198467 p = 1) : d200565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47139 q ha hb
    | true =>
      simp only [d21136, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d198467 q = 1) : d200511 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d198467 q = 1) : d200512 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21265 q = 1) (hb : d198467 q = 1) : d200565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21265, d200565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21265, d200565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47168 (p : Pattern) (ha : d21269 p = 1) (hb : d198467 p = 1) : d200569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d198467 q = 1) : d200540 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47160 q ha hb
    | true =>
      simp only [d21205, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d198467 q = 1) : d200541 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d198467 q = 1) : d200542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d198467 q = 1) : d200543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d198467 q = 1) : d200544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21269 q = 1) (hb : d198467 q = 1) : d200569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21269, d200569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21269, d200569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47169 (p : Pattern) (ha : d21275 p = 1) (hb : d198467 p = 1) : d200572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47138 q ha hb
    | true =>
      simp only [d21132, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d198467 q = 1) : d200548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d198467 q = 1) : d200549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d198467 q = 1) : d200550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21275 q = 1) (hb : d198467 q = 1) : d200572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21275, d200572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21275, d200572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47170 (p : Pattern) (ha : d150083 p = 1) (hb : d198467 p = 1) : d200578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d198467 q = 1) : d200504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47152 q ha hb
    | true =>
      simp only [d21169, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47153 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d198467 q = 1) : d200505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d198467 q = 1) : d200506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d198467 q = 1) : d200507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d198467 q = 1) : d200514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47154 q ha hb
    | true =>
      simp only [d21179, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47155 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d198467 q = 1) : d200515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d198467 q = 1) : d200516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d198467 q = 1) : d200546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47161 q ha hb
    | true =>
      simp only [d21211, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47140 q ha hb
  have h9 (q : Pattern) (ha : d150074 q = 1) (hb : d198467 q = 1) : d200547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150074, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d198467 q = 1) : d200552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47162 q ha hb
    | true =>
      simp only [d21252, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d198467 q = 1) : d200553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150075 q = 1) (hb : d198467 q = 1) : d200554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150076 q = 1) (hb : d198467 q = 1) : d200555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150076, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150077 q = 1) (hb : d198467 q = 1) : d200556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150077, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21260 q = 1) (hb : d198467 q = 1) : d200560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21260, d200560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47164 q ha hb
    | true =>
      simp only [d21260, d200560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47165 q ha hb
  have h16 (q : Pattern) (ha : d21261 q = 1) (hb : d198467 q = 1) : d200561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21261, d200561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21261, d200561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21262 q = 1) (hb : d198467 q = 1) : d200562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21262, d200562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21262, d200562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21263 q = 1) (hb : d198467 q = 1) : d200563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21263, d200563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21263, d200563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21266 q = 1) (hb : d198467 q = 1) : d200566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21266, d200566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47166 q ha hb
    | true =>
      simp only [d21266, d200566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47167 q ha hb
  have h20 (q : Pattern) (ha : d21267 q = 1) (hb : d198467 q = 1) : d200567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21267, d200567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21267, d200567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21268 q = 1) (hb : d198467 q = 1) : d200568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21268, d200568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21268, d200568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21270 q = 1) (hb : d198467 q = 1) : d200570 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47168 q ha hb
    | true =>
      simp only [d21270, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47143 q ha hb
  have h23 (q : Pattern) (ha : d150079 q = 1) (hb : d198467 q = 1) : d200571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150079, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21276 q = 1) (hb : d198467 q = 1) : d200573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47169 q ha hb
    | true =>
      simp only [d21276, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21277 q = 1) (hb : d198467 q = 1) : d200574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21277, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150080 q = 1) (hb : d198467 q = 1) : d200575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150080, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150081 q = 1) (hb : d198467 q = 1) : d200576 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d200576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150081, d200576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150082 q = 1) (hb : d198467 q = 1) : d200577 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d200577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150082, d200577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150083 q = 1) (hb : d198467 q = 1) : d200578 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d200578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150083, d200578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro47171 (p : Pattern) (ha : d150090 p = 1) (hb : d198467 p = 1) : d200598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21270 q = 1) (hb : d198467 q = 1) : d200570 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47168 q ha hb
    | true =>
      simp only [d21270, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47143 q ha hb
  have h2 (q : Pattern) (ha : d150079 q = 1) (hb : d198467 q = 1) : d200571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150079, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21276 q = 1) (hb : d198467 q = 1) : d200573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47169 q ha hb
    | true =>
      simp only [d21276, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21277 q = 1) (hb : d198467 q = 1) : d200574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21277, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150080 q = 1) (hb : d198467 q = 1) : d200575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150080, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150088 q = 1) (hb : d198467 q = 1) : d200596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d200596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150088, d200596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150089 q = 1) (hb : d198467 q = 1) : d200597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d200597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150089, d200597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150090 q = 1) (hb : d198467 q = 1) : d200598 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d200598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150090, d200598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47172 (p : Pattern) (ha : d21319 p = 1) (hb : d198467 p = 1) : d200616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d198467 q = 1) : d200606 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
    | true =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d198467 q = 1) : d200607 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d198467 q = 1) : d200608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d198467 q = 1) : d200609 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21071 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
  have h8 (q : Pattern) (ha : d20990 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
    | true =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21072 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21072, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20991 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21073 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21073, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21074 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21074, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21313 q = 1) (hb : d198467 q = 1) : d200610 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21313, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21314 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
  have h15 (q : Pattern) (ha : d21189 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
    | true =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21315 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21315, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21190 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21316 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21316, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21317 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d21317, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5495 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
  have h21 (q : Pattern) (ha : d5451 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d5496 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d5452 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5497 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d5498 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21318 q = 1) (hb : d198467 q = 1) : d200615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21318, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21318, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d21319 q = 1) (hb : d198467 q = 1) : d200616 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21319, d200616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21319, d200616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro47173 (p : Pattern) (ha : d21323 p = 1) (hb : d198467 p = 1) : d200620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47118 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21076 q = 1) (hb : d198467 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21076, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d198467 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21323 q = 1) (hb : d198467 q = 1) : d200620 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21323, d200620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21323, d200620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47174 (p : Pattern) (ha : d21329 p = 1) (hb : d198467 p = 1) : d200626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21320 q = 1) (hb : d198467 q = 1) : d200617 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21320, d200617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47172 q ha hb
    | true =>
      simp only [d21320, d200617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47131 q ha hb
  have h2 (q : Pattern) (ha : d21321 q = 1) (hb : d198467 q = 1) : d200618 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21321, d200618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21321, d200618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21322 q = 1) (hb : d198467 q = 1) : d200619 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21322, d200619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21322, d200619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21324 q = 1) (hb : d198467 q = 1) : d200621 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21324, d200621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47131 q ha hb
    | true =>
      simp only [d21324, d200621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47173 q ha hb
  have h5 (q : Pattern) (ha : d21325 q = 1) (hb : d198467 q = 1) : d200622 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21325, d200622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21325, d200622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21326 q = 1) (hb : d198467 q = 1) : d200623 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21326, d200623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21326, d200623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21327 q = 1) (hb : d198467 q = 1) : d200624 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21327, d200624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21327, d200624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21078 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47131 q ha hb
    | true =>
      simp only [d21078, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47108 q ha hb
  have h9 (q : Pattern) (ha : d21079 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21080 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20933 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47108 q ha hb
    | true =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20934 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20935 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21081 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21081, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21328 q = 1) (hb : d198467 q = 1) : d200625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21328, d200625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21328, d200625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21329 q = 1) (hb : d198467 q = 1) : d200626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21329, d200626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21329, d200626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro47175 (p : Pattern) (ha : d21334 p = 1) (hb : d198467 p = 1) : d200631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47131 q ha hb
    | true =>
      simp only [d21078, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47108 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20933 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47108 q ha hb
    | true =>
      simp only [d20933, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20934 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20935 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21081 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21332 q = 1) (hb : d198467 q = 1) : d200629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21332, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21333 q = 1) (hb : d198467 q = 1) : d200630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21333, d200630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21333, d200630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21334 q = 1) (hb : d198467 q = 1) : d200631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21334, d200631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21334, d200631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro47176 (p : Pattern) (ha : d21340 p = 1) (hb : d198467 p = 1) : d200637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21330 q = 1) (hb : d198467 q = 1) : d200627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21330, d200627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47174 q ha hb
    | true =>
      simp only [d21330, d200627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21331 q = 1) (hb : d198467 q = 1) : d200628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21331, d200628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21331, d200628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21335 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47175 q ha hb
    | true =>
      simp only [d21335, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21336 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21337 q = 1) (hb : d198467 q = 1) : d200634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21337, d200634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21337, d200634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21338 q = 1) (hb : d198467 q = 1) : d200635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21338, d200635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21338, d200635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21339 q = 1) (hb : d198467 q = 1) : d200636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21339, d200636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21339, d200636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21340 q = 1) (hb : d198467 q = 1) : d200637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21340, d200637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21340, d200637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47177 (p : Pattern) (ha : d21348 p = 1) (hb : d198467 p = 1) : d200645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47175 q ha hb
    | true =>
      simp only [d21335, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21343 q = 1) (hb : d198467 q = 1) : d200640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47149 q ha hb
    | true =>
      simp only [d21343, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21344 q = 1) (hb : d198467 q = 1) : d200641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21345 q = 1) (hb : d198467 q = 1) : d200642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21345, d200642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21345, d200642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21346 q = 1) (hb : d198467 q = 1) : d200643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21346, d200643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21346, d200643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21347 q = 1) (hb : d198467 q = 1) : d200644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21347, d200644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21347, d200644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21348 q = 1) (hb : d198467 q = 1) : d200645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21348, d200645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21348, d200645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47178 (p : Pattern) (ha : d21387 p = 1) (hb : d198467 p = 1) : d200651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47175 q ha hb
    | true =>
      simp only [d21335, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21384 q = 1) (hb : d198467 q = 1) : d200648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21384, d200648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21384, d200648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21385 q = 1) (hb : d198467 q = 1) : d200649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21385, d200649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21385, d200649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21386 q = 1) (hb : d198467 q = 1) : d200650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21386, d200650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21386, d200650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21387 q = 1) (hb : d198467 q = 1) : d200651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21387, d200651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21387, d200651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47179 (p : Pattern) (ha : d150100 p = 1) (hb : d198467 p = 1) : d200657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21349 q = 1) (hb : d198467 q = 1) : d200646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21349, d200646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47176 q ha hb
    | true =>
      simp only [d21349, d200646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47177 q ha hb
  have h2 (q : Pattern) (ha : d150096 q = 1) (hb : d198467 q = 1) : d200647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d200647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150096, d200647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21388 q = 1) (hb : d198467 q = 1) : d200652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21388, d200652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47178 q ha hb
    | true =>
      simp only [d21388, d200652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21389 q = 1) (hb : d198467 q = 1) : d200653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21389, d200653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21389, d200653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150097 q = 1) (hb : d198467 q = 1) : d200654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d200654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150097, d200654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150098 q = 1) (hb : d198467 q = 1) : d200655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d200655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150098, d200655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150099 q = 1) (hb : d198467 q = 1) : d200656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d200656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150099, d200656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150100 q = 1) (hb : d198467 q = 1) : d200657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d200657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150100, d200657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47180 (p : Pattern) (ha : d150106 p = 1) (hb : d198467 p = 1) : d200674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21152 q = 1) (hb : d198467 q = 1) : d200487 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21152, d200487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21152, d200487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47142 q ha hb
  have h2 (q : Pattern) (ha : d21153 q = 1) (hb : d198467 q = 1) : d200488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21153, d200488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21153, d200488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21162 q = 1) (hb : d198467 q = 1) : d200497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47142 q ha hb
    | true =>
      simp only [d21162, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47145 q ha hb
  have h4 (q : Pattern) (ha : d21163 q = 1) (hb : d198467 q = 1) : d200498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21163, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21164 q = 1) (hb : d198467 q = 1) : d200499 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21164, d200499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21164, d200499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150084 q = 1) (hb : d198467 q = 1) : d200579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d200579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47163 q ha hb
    | true =>
      simp only [d150084, d200579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47170 q ha hb
  have h7 (q : Pattern) (ha : d21295 q = 1) (hb : d198467 q = 1) : d200592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21295, d200592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47146 q ha hb
    | true =>
      simp only [d21295, d200592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47147 q ha hb
  have h8 (q : Pattern) (ha : d150085 q = 1) (hb : d198467 q = 1) : d200593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d200593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150085, d200593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150086 q = 1) (hb : d198467 q = 1) : d200594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d200594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150086, d200594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150087 q = 1) (hb : d198467 q = 1) : d200595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d200595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150087, d200595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150091 q = 1) (hb : d198467 q = 1) : d200599 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d200599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150091, d200599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47171 q ha hb
  have h12 (q : Pattern) (ha : d21304 q = 1) (hb : d198467 q = 1) : d200601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21304, d200601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21304, d200601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47148 q ha hb
  have h13 (q : Pattern) (ha : d150092 q = 1) (hb : d198467 q = 1) : d200602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d200602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150092, d200602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150093 q = 1) (hb : d198467 q = 1) : d200603 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d200603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150093, d200603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150094 q = 1) (hb : d198467 q = 1) : d200604 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d200604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150094, d200604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150095 q = 1) (hb : d198467 q = 1) : d200605 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d200605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150095, d200605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150101 q = 1) (hb : d198467 q = 1) : d200658 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d200658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150101, d200658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47179 q ha hb
  have h18 (q : Pattern) (ha : d21405 q = 1) (hb : d198467 q = 1) : d200669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21405, d200669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21405, d200669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47151 q ha hb
  have h19 (q : Pattern) (ha : d150102 q = 1) (hb : d198467 q = 1) : d200670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d200670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150102, d200670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150103 q = 1) (hb : d198467 q = 1) : d200671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d200671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150103, d200671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150104 q = 1) (hb : d198467 q = 1) : d200672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d200672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150104, d200672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150105 q = 1) (hb : d198467 q = 1) : d200673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d200673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150105, d200673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150106 q = 1) (hb : d198467 q = 1) : d200674 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d200674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150106, d200674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro47181 (p : Pattern) (ha : d150112 p = 1) (hb : d198467 p = 1) : d200680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150107 q = 1) (hb : d198467 q = 1) : d200675 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d200675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150107, d200675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47180 q ha hb
  have h2 (q : Pattern) (ha : d150108 q = 1) (hb : d198467 q = 1) : d200676 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d200676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150108, d200676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150109 q = 1) (hb : d198467 q = 1) : d200677 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d200677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150109, d200677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150110 q = 1) (hb : d198467 q = 1) : d200678 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d200678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150110, d200678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150111 q = 1) (hb : d198467 q = 1) : d200679 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d200679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150111, d200679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150112 q = 1) (hb : d198467 q = 1) : d200680 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d200680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150112, d200680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47182 (p : Pattern) (ha : d762 p = 1) (hb : d198467 p = 1) : d25703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d198467 q = 1) : d25698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d198467 q = 1) : d25703 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d25703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d25703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47183 (p : Pattern) (ha : d21419 p = 1) (hb : d198467 p = 1) : d200683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
    | true =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20990 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
    | true =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20991 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20992 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20993 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20993, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21187 q = 1) (hb : d198467 q = 1) : d200522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21187, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21189 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
    | true =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21190 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21191 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21192 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21192, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21418 q = 1) (hb : d198467 q = 1) : d200682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21418, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21419 q = 1) (hb : d198467 q = 1) : d200683 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21419, d200683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21419, d200683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47184 (p : Pattern) (ha : d21420 p = 1) (hb : d198467 p = 1) : d200684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
    | true =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d198467 q = 1) : d200352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d198467 q = 1) : d25698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21420 q = 1) (hb : d198467 q = 1) : d200684 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21420, d200684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21420, d200684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47185 (p : Pattern) (ha : d21430 p = 1) (hb : d198467 p = 1) : d200694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21421 q = 1) (hb : d198467 q = 1) : d200685 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47183 q ha hb
    | true =>
      simp only [d21421, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47184 q ha hb
  have h2 (q : Pattern) (ha : d21422 q = 1) (hb : d198467 q = 1) : d200686 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21423 q = 1) (hb : d198467 q = 1) : d200687 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21424 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47184 q ha hb
    | true =>
      simp only [d21424, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47182 q ha hb
  have h5 (q : Pattern) (ha : d21425 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21426 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21427 q = 1) (hb : d198467 q = 1) : d200691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21427, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21428 q = 1) (hb : d198467 q = 1) : d200692 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21428, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21429 q = 1) (hb : d198467 q = 1) : d200693 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21429, d200693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21429, d200693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21430 q = 1) (hb : d198467 q = 1) : d200694 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21430, d200694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21430, d200694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro47186 (p : Pattern) (ha : d21434 p = 1) (hb : d198467 p = 1) : d200698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21424 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47184 q ha hb
    | true =>
      simp only [d21424, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47182 q ha hb
  have h2 (q : Pattern) (ha : d21425 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21426 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21428 q = 1) (hb : d198467 q = 1) : d200692 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21428, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21433 q = 1) (hb : d198467 q = 1) : d200697 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21433, d200697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21433, d200697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21434 q = 1) (hb : d198467 q = 1) : d200698 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21434, d200698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21434, d200698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47187 (p : Pattern) (ha : d21440 p = 1) (hb : d198467 p = 1) : d200704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d198467 q = 1) : d200703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21440 q = 1) (hb : d198467 q = 1) : d200704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21440, d200704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21440, d200704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47188 (p : Pattern) (ha : d21444 p = 1) (hb : d198467 p = 1) : d200708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d198467 q = 1) : d200707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21444 q = 1) (hb : d198467 q = 1) : d200708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21444, d200708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21444, d200708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47189 (p : Pattern) (ha : d21450 p = 1) (hb : d198467 p = 1) : d200714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47187 q ha hb
    | true =>
      simp only [d21445, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47188 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21450 q = 1) (hb : d198467 q = 1) : d200714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47190 (p : Pattern) (ha : d21453 p = 1) (hb : d198467 p = 1) : d200717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d198467 q = 1) : d200703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21453 q = 1) (hb : d198467 q = 1) : d200717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21453, d200717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21453, d200717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47191 (p : Pattern) (ha : d21454 p = 1) (hb : d198467 p = 1) : d200718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d198467 q = 1) : d200707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21454 q = 1) (hb : d198467 q = 1) : d200718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21454, d200718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21454, d200718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47192 (p : Pattern) (ha : d21460 p = 1) (hb : d198467 p = 1) : d200724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47187 q ha hb
    | true =>
      simp only [d21445, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47188 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21455 q = 1) (hb : d198467 q = 1) : d200719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47190 q ha hb
    | true =>
      simp only [d21455, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47191 q ha hb
  have h7 (q : Pattern) (ha : d21456 q = 1) (hb : d198467 q = 1) : d200720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21457 q = 1) (hb : d198467 q = 1) : d200721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21457, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21458 q = 1) (hb : d198467 q = 1) : d200722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21459 q = 1) (hb : d198467 q = 1) : d200723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21460 q = 1) (hb : d198467 q = 1) : d200724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21460, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47193 (p : Pattern) (ha : d21591 p = 1) (hb : d198467 p = 1) : d200813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47187 q ha hb
    | true =>
      simp only [d21445, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47188 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21586 q = 1) (hb : d198467 q = 1) : d200808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47188 q ha hb
    | true =>
      simp only [d21586, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21587 q = 1) (hb : d198467 q = 1) : d200809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21588 q = 1) (hb : d198467 q = 1) : d200810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21588, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21589 q = 1) (hb : d198467 q = 1) : d200811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21590 q = 1) (hb : d198467 q = 1) : d200812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21591 q = 1) (hb : d198467 q = 1) : d200813 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21591, d200813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21591, d200813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47194 (p : Pattern) (ha : d21597 p = 1) (hb : d198467 p = 1) : d200819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21586 q = 1) (hb : d198467 q = 1) : d200808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47188 q ha hb
    | true =>
      simp only [d21586, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21587 q = 1) (hb : d198467 q = 1) : d200809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21588 q = 1) (hb : d198467 q = 1) : d200810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21588, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21589 q = 1) (hb : d198467 q = 1) : d200811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21590 q = 1) (hb : d198467 q = 1) : d200812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21592 q = 1) (hb : d198467 q = 1) : d200814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47191 q ha hb
    | true =>
      simp only [d21592, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21593 q = 1) (hb : d198467 q = 1) : d200815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21594 q = 1) (hb : d198467 q = 1) : d200816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21594, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21595 q = 1) (hb : d198467 q = 1) : d200817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21596 q = 1) (hb : d198467 q = 1) : d200818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21597 q = 1) (hb : d198467 q = 1) : d200819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21597, d200819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21597, d200819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47195 (p : Pattern) (ha : d21606 p = 1) (hb : d198467 p = 1) : d200828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21592 q = 1) (hb : d198467 q = 1) : d200814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47191 q ha hb
    | true =>
      simp only [d21592, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21593 q = 1) (hb : d198467 q = 1) : d200815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21594 q = 1) (hb : d198467 q = 1) : d200816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21594, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21595 q = 1) (hb : d198467 q = 1) : d200817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21596 q = 1) (hb : d198467 q = 1) : d200818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21606 q = 1) (hb : d198467 q = 1) : d200828 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21606, d200828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21606, d200828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47196 (p : Pattern) (ha : d986 p = 1) (hb : d198467 p = 1) : d25968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d198467 q = 1) : d25957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d986 q = 1) (hb : d198467 q = 1) : d25968 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d25968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d25968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47197 (p : Pattern) (ha : d21633 p = 1) (hb : d198467 p = 1) : d200855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
    | true =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d198467 q = 1) : d200421 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d198467 q = 1) : d25957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21633 q = 1) (hb : d198467 q = 1) : d200855 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21633, d200855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21633, d200855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47198 (p : Pattern) (ha : d21655 p = 1) (hb : d198467 p = 1) : d200877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21637 q = 1) (hb : d198467 q = 1) : d200859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47197 q ha hb
    | true =>
      simp only [d21637, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47196 q ha hb
  have h2 (q : Pattern) (ha : d21638 q = 1) (hb : d198467 q = 1) : d200860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21639 q = 1) (hb : d198467 q = 1) : d200861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21645 q = 1) (hb : d198467 q = 1) : d200867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21645, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21654 q = 1) (hb : d198467 q = 1) : d200876 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21654, d200876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21654, d200876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21655 q = 1) (hb : d198467 q = 1) : d200877 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21655, d200877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21655, d200877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47199 (p : Pattern) (ha : d21715 p = 1) (hb : d198467 p = 1) : d200900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21656 q = 1) (hb : d198467 q = 1) : d200878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47198 q ha hb
    | true =>
      simp only [d21656, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21657 q = 1) (hb : d198467 q = 1) : d200879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21712 q = 1) (hb : d198467 q = 1) : d200897 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21712, d200897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21712, d200897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21713 q = 1) (hb : d198467 q = 1) : d200898 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21713, d200898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21713, d200898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21714 q = 1) (hb : d198467 q = 1) : d200899 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21714, d200899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21714, d200899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21715 q = 1) (hb : d198467 q = 1) : d200900 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21715, d200900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21715, d200900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47200 (p : Pattern) (ha : d21721 p = 1) (hb : d198467 p = 1) : d200906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21716 q = 1) (hb : d198467 q = 1) : d200901 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21716, d200901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47199 q ha hb
    | true =>
      simp only [d21716, d200901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21717 q = 1) (hb : d198467 q = 1) : d200902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21717, d200902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21717, d200902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21718 q = 1) (hb : d198467 q = 1) : d200903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21718, d200903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21718, d200903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21719 q = 1) (hb : d198467 q = 1) : d200904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21719, d200904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21719, d200904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21720 q = 1) (hb : d198467 q = 1) : d200905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21720, d200905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21720, d200905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21721 q = 1) (hb : d198467 q = 1) : d200906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21721, d200906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21721, d200906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47201 (p : Pattern) (ha : d21465 p = 1) (hb : d198467 p = 1) : d200729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d198467 q = 1) : d200728 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21465 q = 1) (hb : d198467 q = 1) : d200729 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21465, d200729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21465, d200729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47202 (p : Pattern) (ha : d21467 p = 1) (hb : d198467 p = 1) : d200731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d198467 q = 1) : d200730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21467 q = 1) (hb : d198467 q = 1) : d200731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21467, d200731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21467, d200731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47203 (p : Pattern) (ha : d21474 p = 1) (hb : d198467 p = 1) : d200738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d198467 q = 1) : d200736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d198467 q = 1) : d200737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21474 q = 1) (hb : d198467 q = 1) : d200738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21474, d200738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21474, d200738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47204 (p : Pattern) (ha : d21477 p = 1) (hb : d198467 p = 1) : d200741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d198467 q = 1) : d200739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d198467 q = 1) : d200740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21477 q = 1) (hb : d198467 q = 1) : d200741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21477, d200741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21477, d200741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47205 (p : Pattern) (ha : d21481 p = 1) (hb : d198467 p = 1) : d200745 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d823 q = 1) : d823 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d824 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d824, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d829 q = 1) : d829 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d830 q = 1) (hb : d152852 q = 1) : d25761 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d831 q = 1) (hb : d152852 q = 1) : d25762 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d831, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d831, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d832 q = 1) (hb : d152852 q = 1) : d25763 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d832, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d832, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21481 q = 1) (hb : d198467 q = 1) : d200745 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21481, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21481, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47206 (p : Pattern) (ha : d21487 p = 1) (hb : d198467 p = 1) : d200751 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d532 q = 1) : d532 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9593 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9593, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9593, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9594 q = 1) (hb : d152852 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9594, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9594, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9595 q = 1) (hb : d152852 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9595, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9595, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21487 q = 1) (hb : d198467 q = 1) : d200751 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21487, d198467, d200751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21487, d198467, d200751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47207 (p : Pattern) (ha : d21493 p = 1) (hb : d198467 p = 1) : d200757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21482 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47205 q ha hb
    | true =>
      simp only [d21482, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21483 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21483, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21484 q = 1) (hb : d198467 q = 1) : d200748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21484, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21484, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21485 q = 1) (hb : d198467 q = 1) : d200749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21485, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21485, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21183 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
    | true =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21184 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21185 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21186 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21186, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21486 q = 1) (hb : d198467 q = 1) : d200750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21486, d200750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21486, d200750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21488 q = 1) (hb : d198467 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47206 q ha hb
    | true =>
      simp only [d21488, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21489 q = 1) (hb : d198467 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21489, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21490 q = 1) (hb : d198467 q = 1) : d200754 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21490, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21490, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21491 q = 1) (hb : d198467 q = 1) : d200755 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21491, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21491, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d21189 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
    | true =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21190 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21191 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21192 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21192, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21492 q = 1) (hb : d198467 q = 1) : d200756 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21492, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21492, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21493 q = 1) (hb : d198467 q = 1) : d200757 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21493, d200757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21493, d200757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47208 (p : Pattern) (ha : d21497 p = 1) (hb : d198467 p = 1) : d200761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21189 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
    | true =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21190 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21191 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21192 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21192, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21418 q = 1) (hb : d198467 q = 1) : d200682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21418, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d198467 q = 1) : d25698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21497 q = 1) (hb : d198467 q = 1) : d200761 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21497, d200761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21497, d200761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47209 (p : Pattern) (ha : d21503 p = 1) (hb : d198467 p = 1) : d200767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21494 q = 1) (hb : d198467 q = 1) : d200758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21494, d200758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47207 q ha hb
    | true =>
      simp only [d21494, d200758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47183 q ha hb
  have h2 (q : Pattern) (ha : d21495 q = 1) (hb : d198467 q = 1) : d200759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21495, d200759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21495, d200759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21496 q = 1) (hb : d198467 q = 1) : d200760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21496, d200760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21496, d200760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21498 q = 1) (hb : d198467 q = 1) : d200762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21498, d200762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47183 q ha hb
    | true =>
      simp only [d21498, d200762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47208 q ha hb
  have h5 (q : Pattern) (ha : d21499 q = 1) (hb : d198467 q = 1) : d200763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21499, d200763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21499, d200763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21500 q = 1) (hb : d198467 q = 1) : d200764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21500, d200764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21500, d200764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21501 q = 1) (hb : d198467 q = 1) : d200765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21501, d200765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21501, d200765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21421 q = 1) (hb : d198467 q = 1) : d200685 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47183 q ha hb
    | true =>
      simp only [d21421, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47184 q ha hb
  have h9 (q : Pattern) (ha : d21422 q = 1) (hb : d198467 q = 1) : d200686 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21423 q = 1) (hb : d198467 q = 1) : d200687 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21424 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47184 q ha hb
    | true =>
      simp only [d21424, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47182 q ha hb
  have h12 (q : Pattern) (ha : d21425 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21426 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21427 q = 1) (hb : d198467 q = 1) : d200691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21427, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21502 q = 1) (hb : d198467 q = 1) : d200766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21502, d200766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21502, d200766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21503 q = 1) (hb : d198467 q = 1) : d200767 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21503, d200767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21503, d200767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro47210 (p : Pattern) (ha : d21509 p = 1) (hb : d198467 p = 1) : d200773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d198467 q = 1) : d200768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47209 q ha hb
    | true =>
      simp only [d21504, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d198467 q = 1) : d200769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d198467 q = 1) : d200770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d198467 q = 1) : d200771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d198467 q = 1) : d200772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21509 q = 1) (hb : d198467 q = 1) : d200773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21509, d200773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21509, d200773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47211 (p : Pattern) (ha : d21554 p = 1) (hb : d198467 p = 1) : d200779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d198467 q = 1) : d200776 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d198467 q = 1) : d200777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d198467 q = 1) : d200778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21554 q = 1) (hb : d198467 q = 1) : d200779 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21554, d200779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21554, d200779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47212 (p : Pattern) (ha : d150118 p = 1) (hb : d198467 p = 1) : d200785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d198467 q = 1) : d200732 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d200732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47201 q ha hb
    | true =>
      simp only [d21468, d200732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47202 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d198467 q = 1) : d200733 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d200733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d200733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d198467 q = 1) : d200734 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d200734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d200734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d198467 q = 1) : d200735 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d200735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d200735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d198467 q = 1) : d200742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d200742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47203 q ha hb
    | true =>
      simp only [d21478, d200742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47204 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d198467 q = 1) : d200743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d200743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d200743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d198467 q = 1) : d200744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d200744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d200744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d198467 q = 1) : d200774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d200774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47210 q ha hb
    | true =>
      simp only [d21510, d200774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47187 q ha hb
  have h9 (q : Pattern) (ha : d150114 q = 1) (hb : d198467 q = 1) : d200775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d200775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150114, d200775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d198467 q = 1) : d200780 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d200780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47211 q ha hb
    | true =>
      simp only [d21555, d200780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d198467 q = 1) : d200781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d200781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d200781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150115 q = 1) (hb : d198467 q = 1) : d200782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d200782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d200782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150116 q = 1) (hb : d198467 q = 1) : d200783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d200783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150116, d200783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150117 q = 1) (hb : d198467 q = 1) : d200784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d200784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150117, d200784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150118 q = 1) (hb : d198467 q = 1) : d200785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d200785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150118, d200785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47213 (p : Pattern) (ha : d21561 p = 1) (hb : d198467 p = 1) : d200786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d198467 q = 1) : d200728 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21561 q = 1) (hb : d198467 q = 1) : d200786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21561, d200786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21561, d200786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47214 (p : Pattern) (ha : d21562 p = 1) (hb : d198467 p = 1) : d200787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d198467 q = 1) : d200730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21562 q = 1) (hb : d198467 q = 1) : d200787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21562, d200787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21562, d200787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47215 (p : Pattern) (ha : d21567 p = 1) (hb : d198467 p = 1) : d200792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d198467 q = 1) : d200736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d198467 q = 1) : d200737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21567 q = 1) (hb : d198467 q = 1) : d200792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21567, d200792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21567, d200792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47216 (p : Pattern) (ha : d21568 p = 1) (hb : d198467 p = 1) : d200793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47186 q ha hb
    | true =>
      simp only [d21435, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d198467 q = 1) : d200739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d198467 q = 1) : d200740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21568 q = 1) (hb : d198467 q = 1) : d200793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21568, d200793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21568, d200793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47217 (p : Pattern) (ha : d21572 p = 1) (hb : d198467 p = 1) : d200797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d198467 q = 1) : d200768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47209 q ha hb
    | true =>
      simp only [d21504, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d198467 q = 1) : d200769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d198467 q = 1) : d200770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d198467 q = 1) : d200771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d198467 q = 1) : d200772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21572 q = 1) (hb : d198467 q = 1) : d200797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21572, d200797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21572, d200797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47218 (p : Pattern) (ha : d21578 p = 1) (hb : d198467 p = 1) : d200800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47185 q ha hb
    | true =>
      simp only [d21431, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d198467 q = 1) : d200776 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d198467 q = 1) : d200777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d198467 q = 1) : d200778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21578 q = 1) (hb : d198467 q = 1) : d200800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21578, d200800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21578, d200800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47219 (p : Pattern) (ha : d150123 p = 1) (hb : d198467 p = 1) : d200806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d198467 q = 1) : d200732 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d200732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47201 q ha hb
    | true =>
      simp only [d21468, d200732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47202 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d198467 q = 1) : d200733 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d200733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d200733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d198467 q = 1) : d200734 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d200734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d200734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d198467 q = 1) : d200735 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d200735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d200735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d198467 q = 1) : d200742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d200742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47203 q ha hb
    | true =>
      simp only [d21478, d200742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47204 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d198467 q = 1) : d200743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d200743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d200743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d198467 q = 1) : d200744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d200744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d200744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d198467 q = 1) : d200774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d200774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47210 q ha hb
    | true =>
      simp only [d21510, d200774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47187 q ha hb
  have h9 (q : Pattern) (ha : d150114 q = 1) (hb : d198467 q = 1) : d200775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d200775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150114, d200775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d198467 q = 1) : d200780 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d200780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47211 q ha hb
    | true =>
      simp only [d21555, d200780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d198467 q = 1) : d200781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d200781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d200781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150115 q = 1) (hb : d198467 q = 1) : d200782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d200782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d200782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150116 q = 1) (hb : d198467 q = 1) : d200783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d200783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150116, d200783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150117 q = 1) (hb : d198467 q = 1) : d200784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d200784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150117, d200784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21563 q = 1) (hb : d198467 q = 1) : d200788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21563, d200788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47213 q ha hb
    | true =>
      simp only [d21563, d200788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47214 q ha hb
  have h16 (q : Pattern) (ha : d21564 q = 1) (hb : d198467 q = 1) : d200789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21564, d200789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21564, d200789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21565 q = 1) (hb : d198467 q = 1) : d200790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21565, d200790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21565, d200790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21566 q = 1) (hb : d198467 q = 1) : d200791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21566, d200791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21566, d200791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21569 q = 1) (hb : d198467 q = 1) : d200794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21569, d200794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47215 q ha hb
    | true =>
      simp only [d21569, d200794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47216 q ha hb
  have h20 (q : Pattern) (ha : d21570 q = 1) (hb : d198467 q = 1) : d200795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21570, d200795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21570, d200795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21571 q = 1) (hb : d198467 q = 1) : d200796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21571, d200796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21571, d200796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21573 q = 1) (hb : d198467 q = 1) : d200798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d200798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47217 q ha hb
    | true =>
      simp only [d21573, d200798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47190 q ha hb
  have h23 (q : Pattern) (ha : d150119 q = 1) (hb : d198467 q = 1) : d200799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d200799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150119, d200799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21579 q = 1) (hb : d198467 q = 1) : d200801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d200801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47218 q ha hb
    | true =>
      simp only [d21579, d200801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21580 q = 1) (hb : d198467 q = 1) : d200802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d200802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21580, d200802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150120 q = 1) (hb : d198467 q = 1) : d200803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d200803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150120, d200803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150121 q = 1) (hb : d198467 q = 1) : d200804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d200804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150121, d200804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150122 q = 1) (hb : d198467 q = 1) : d200805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d200805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150122, d200805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150123 q = 1) (hb : d198467 q = 1) : d200806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d200806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150123, d200806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro47220 (p : Pattern) (ha : d150130 p = 1) (hb : d198467 p = 1) : d200826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21573 q = 1) (hb : d198467 q = 1) : d200798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d200798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47217 q ha hb
    | true =>
      simp only [d21573, d200798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47190 q ha hb
  have h2 (q : Pattern) (ha : d150119 q = 1) (hb : d198467 q = 1) : d200799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d200799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150119, d200799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21579 q = 1) (hb : d198467 q = 1) : d200801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d200801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47218 q ha hb
    | true =>
      simp only [d21579, d200801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21580 q = 1) (hb : d198467 q = 1) : d200802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d200802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21580, d200802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150120 q = 1) (hb : d198467 q = 1) : d200803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d200803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150120, d200803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150128 q = 1) (hb : d198467 q = 1) : d200824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d200824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150128, d200824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150129 q = 1) (hb : d198467 q = 1) : d200825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d200825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150129, d200825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150130 q = 1) (hb : d198467 q = 1) : d200826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d200826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150130, d200826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47221 (p : Pattern) (ha : d21622 p = 1) (hb : d198467 p = 1) : d200844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21612 q = 1) (hb : d198467 q = 1) : d200834 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21612, d200834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21612, d200834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47205 q ha hb
  have h2 (q : Pattern) (ha : d21482 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47205 q ha hb
    | true =>
      simp only [d21482, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21613 q = 1) (hb : d198467 q = 1) : d200835 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21613, d200835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21613, d200835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21483 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21483, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21614 q = 1) (hb : d198467 q = 1) : d200836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21614, d200836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21614, d200836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21615 q = 1) (hb : d198467 q = 1) : d200837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21615, d200837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21615, d200837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21309 q = 1) (hb : d198467 q = 1) : d200606 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
  have h8 (q : Pattern) (ha : d21183 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
    | true =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21310 q = 1) (hb : d198467 q = 1) : d200607 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21310, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21184 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21311 q = 1) (hb : d198467 q = 1) : d200608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21311, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21312 q = 1) (hb : d198467 q = 1) : d200609 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21312, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21616 q = 1) (hb : d198467 q = 1) : d200838 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21616, d200838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21616, d200838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21617 q = 1) (hb : d198467 q = 1) : d200839 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21617, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21617, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47206 q ha hb
  have h15 (q : Pattern) (ha : d21488 q = 1) (hb : d198467 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47206 q ha hb
    | true =>
      simp only [d21488, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21618 q = 1) (hb : d198467 q = 1) : d200840 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21618, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21618, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21489 q = 1) (hb : d198467 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21489, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21619 q = 1) (hb : d198467 q = 1) : d200841 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21619, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21619, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21620 q = 1) (hb : d198467 q = 1) : d200842 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21620, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d21620, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d21314 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
  have h21 (q : Pattern) (ha : d21189 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
    | true =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21315 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21315, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d21190 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21316 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d21316, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d21317 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21317, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21621 q = 1) (hb : d198467 q = 1) : d200843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21621, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21621, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d21622 q = 1) (hb : d198467 q = 1) : d200844 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21622, d200844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21622, d200844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro47222 (p : Pattern) (ha : d21624 p = 1) (hb : d198467 p = 1) : d200846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d198467 q = 1) : d200606 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47156 q ha hb
    | true =>
      simp only [d21183, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d198467 q = 1) : d200607 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d198467 q = 1) : d200608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d198467 q = 1) : d200609 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21071 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
  have h8 (q : Pattern) (ha : d20990 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47119 q ha hb
    | true =>
      simp only [d20990, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21072 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21072, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20991 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20991, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21073 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21073, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21074 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21074, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21313 q = 1) (hb : d198467 q = 1) : d200610 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21313, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21314 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
  have h15 (q : Pattern) (ha : d21189 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
    | true =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21315 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21315, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21190 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21316 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21316, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21317 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d21317, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21623 q = 1) (hb : d198467 q = 1) : d200845 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d200845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21623, d200845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d21624 q = 1) (hb : d198467 q = 1) : d200846 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21624, d200846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21624, d200846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro47223 (p : Pattern) (ha : d21628 p = 1) (hb : d198467 p = 1) : d200850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21314 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
  have h2 (q : Pattern) (ha : d21189 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47157 q ha hb
    | true =>
      simp only [d21189, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21315 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21315, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21190 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21190, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21316 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21316, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21317 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21317, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21623 q = 1) (hb : d198467 q = 1) : d200845 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d200845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21623, d200845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d198467 q = 1) : d25957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21628 q = 1) (hb : d198467 q = 1) : d200850 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21628, d200850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21628, d200850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47224 (p : Pattern) (ha : d21642 p = 1) (hb : d198467 p = 1) : d200864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21625 q = 1) (hb : d198467 q = 1) : d200847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21625, d200847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47221 q ha hb
    | true =>
      simp only [d21625, d200847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47222 q ha hb
  have h2 (q : Pattern) (ha : d21626 q = 1) (hb : d198467 q = 1) : d200848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21626, d200848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21626, d200848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21627 q = 1) (hb : d198467 q = 1) : d200849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21627, d200849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21627, d200849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21629 q = 1) (hb : d198467 q = 1) : d200851 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21629, d200851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47222 q ha hb
    | true =>
      simp only [d21629, d200851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47223 q ha hb
  have h5 (q : Pattern) (ha : d21630 q = 1) (hb : d198467 q = 1) : d200852 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21630, d200852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21630, d200852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21631 q = 1) (hb : d198467 q = 1) : d200853 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21631, d200853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21631, d200853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21632 q = 1) (hb : d198467 q = 1) : d200854 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21632, d200854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21632, d200854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21634 q = 1) (hb : d198467 q = 1) : d200856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d200856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47222 q ha hb
    | true =>
      simp only [d21634, d200856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47197 q ha hb
  have h9 (q : Pattern) (ha : d21635 q = 1) (hb : d198467 q = 1) : d200857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d200857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d200857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21636 q = 1) (hb : d198467 q = 1) : d200858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d200858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d200858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21637 q = 1) (hb : d198467 q = 1) : d200859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47197 q ha hb
    | true =>
      simp only [d21637, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47196 q ha hb
  have h12 (q : Pattern) (ha : d21638 q = 1) (hb : d198467 q = 1) : d200860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21639 q = 1) (hb : d198467 q = 1) : d200861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21640 q = 1) (hb : d198467 q = 1) : d200862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d200862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21640, d200862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21641 q = 1) (hb : d198467 q = 1) : d200863 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21641, d200863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21641, d200863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21642 q = 1) (hb : d198467 q = 1) : d200864 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21642, d200864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21642, d200864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro47225 (p : Pattern) (ha : d21647 p = 1) (hb : d198467 p = 1) : d200869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21634 q = 1) (hb : d198467 q = 1) : d200856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d200856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47222 q ha hb
    | true =>
      simp only [d21634, d200856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47197 q ha hb
  have h2 (q : Pattern) (ha : d21635 q = 1) (hb : d198467 q = 1) : d200857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d200857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d200857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21636 q = 1) (hb : d198467 q = 1) : d200858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d200858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d200858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21637 q = 1) (hb : d198467 q = 1) : d200859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47197 q ha hb
    | true =>
      simp only [d21637, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47196 q ha hb
  have h5 (q : Pattern) (ha : d21638 q = 1) (hb : d198467 q = 1) : d200860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21639 q = 1) (hb : d198467 q = 1) : d200861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21640 q = 1) (hb : d198467 q = 1) : d200862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d200862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21640, d200862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21645 q = 1) (hb : d198467 q = 1) : d200867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21645, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21646 q = 1) (hb : d198467 q = 1) : d200868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21646, d200868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21646, d200868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21647 q = 1) (hb : d198467 q = 1) : d200869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21647, d200869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21647, d200869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro47226 (p : Pattern) (ha : d21653 p = 1) (hb : d198467 p = 1) : d200875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21643 q = 1) (hb : d198467 q = 1) : d200865 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21643, d200865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47224 q ha hb
    | true =>
      simp only [d21643, d200865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21644 q = 1) (hb : d198467 q = 1) : d200866 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21644, d200866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21644, d200866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21648 q = 1) (hb : d198467 q = 1) : d200870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47225 q ha hb
    | true =>
      simp only [d21648, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21649 q = 1) (hb : d198467 q = 1) : d200871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21650 q = 1) (hb : d198467 q = 1) : d200872 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21650, d200872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21650, d200872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21651 q = 1) (hb : d198467 q = 1) : d200873 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21651, d200873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21651, d200873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21652 q = 1) (hb : d198467 q = 1) : d200874 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21652, d200874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21652, d200874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21653 q = 1) (hb : d198467 q = 1) : d200875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21653, d200875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21653, d200875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47227 (p : Pattern) (ha : d21661 p = 1) (hb : d198467 p = 1) : d200883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d198467 q = 1) : d200870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47225 q ha hb
    | true =>
      simp only [d21648, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d198467 q = 1) : d200871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21656 q = 1) (hb : d198467 q = 1) : d200878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47198 q ha hb
    | true =>
      simp only [d21656, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21657 q = 1) (hb : d198467 q = 1) : d200879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21658 q = 1) (hb : d198467 q = 1) : d200880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21658, d200880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21658, d200880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21659 q = 1) (hb : d198467 q = 1) : d200881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21659, d200881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21659, d200881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21660 q = 1) (hb : d198467 q = 1) : d200882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21660, d200882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21660, d200882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21661 q = 1) (hb : d198467 q = 1) : d200883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21661, d200883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21661, d200883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47228 (p : Pattern) (ha : d21704 p = 1) (hb : d198467 p = 1) : d200889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d198467 q = 1) : d200870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47225 q ha hb
    | true =>
      simp only [d21648, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d198467 q = 1) : d200871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21701 q = 1) (hb : d198467 q = 1) : d200886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21701, d200886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21701, d200886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21702 q = 1) (hb : d198467 q = 1) : d200887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21702, d200887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21702, d200887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21703 q = 1) (hb : d198467 q = 1) : d200888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21703, d200888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21703, d200888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21704 q = 1) (hb : d198467 q = 1) : d200889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21704, d200889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21704, d200889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47229 (p : Pattern) (ha : d150140 p = 1) (hb : d198467 p = 1) : d200895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21662 q = 1) (hb : d198467 q = 1) : d200884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21662, d200884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47226 q ha hb
    | true =>
      simp only [d21662, d200884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47227 q ha hb
  have h2 (q : Pattern) (ha : d150136 q = 1) (hb : d198467 q = 1) : d200885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d200885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150136, d200885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21705 q = 1) (hb : d198467 q = 1) : d200890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21705, d200890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47228 q ha hb
    | true =>
      simp only [d21705, d200890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21706 q = 1) (hb : d198467 q = 1) : d200891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21706, d200891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21706, d200891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150137 q = 1) (hb : d198467 q = 1) : d200892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d200892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150137, d200892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150138 q = 1) (hb : d198467 q = 1) : d200893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d200893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150138, d200893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150139 q = 1) (hb : d198467 q = 1) : d200894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d200894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150139, d200894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150140 q = 1) (hb : d198467 q = 1) : d200895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d200895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150140, d200895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47230 (p : Pattern) (ha : d150146 p = 1) (hb : d198467 p = 1) : d200912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21451 q = 1) (hb : d198467 q = 1) : d200715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21451, d200715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21451, d200715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47189 q ha hb
  have h2 (q : Pattern) (ha : d21452 q = 1) (hb : d198467 q = 1) : d200716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21452, d200716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21452, d200716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21461 q = 1) (hb : d198467 q = 1) : d200725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47189 q ha hb
    | true =>
      simp only [d21461, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47192 q ha hb
  have h4 (q : Pattern) (ha : d21462 q = 1) (hb : d198467 q = 1) : d200726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21462, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21463 q = 1) (hb : d198467 q = 1) : d200727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21463, d200727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21463, d200727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150124 q = 1) (hb : d198467 q = 1) : d200807 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d200807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47212 q ha hb
    | true =>
      simp only [d150124, d200807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47219 q ha hb
  have h7 (q : Pattern) (ha : d21598 q = 1) (hb : d198467 q = 1) : d200820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21598, d200820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47193 q ha hb
    | true =>
      simp only [d21598, d200820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47194 q ha hb
  have h8 (q : Pattern) (ha : d150125 q = 1) (hb : d198467 q = 1) : d200821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d200821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150125, d200821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150126 q = 1) (hb : d198467 q = 1) : d200822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d200822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150126, d200822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150127 q = 1) (hb : d198467 q = 1) : d200823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d200823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150127, d200823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150131 q = 1) (hb : d198467 q = 1) : d200827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d200827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150131, d200827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47220 q ha hb
  have h12 (q : Pattern) (ha : d21607 q = 1) (hb : d198467 q = 1) : d200829 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21607, d200829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21607, d200829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47195 q ha hb
  have h13 (q : Pattern) (ha : d150132 q = 1) (hb : d198467 q = 1) : d200830 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d200830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150132, d200830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150133 q = 1) (hb : d198467 q = 1) : d200831 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d200831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150133, d200831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150134 q = 1) (hb : d198467 q = 1) : d200832 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d200832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150134, d200832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150135 q = 1) (hb : d198467 q = 1) : d200833 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d200833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150135, d200833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150141 q = 1) (hb : d198467 q = 1) : d200896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d200896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150141, d200896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47229 q ha hb
  have h18 (q : Pattern) (ha : d21722 q = 1) (hb : d198467 q = 1) : d200907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21722, d200907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21722, d200907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47200 q ha hb
  have h19 (q : Pattern) (ha : d150142 q = 1) (hb : d198467 q = 1) : d200908 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d200908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150142, d200908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150143 q = 1) (hb : d198467 q = 1) : d200909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d200909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150143, d200909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150144 q = 1) (hb : d198467 q = 1) : d200910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d200910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150144, d200910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150145 q = 1) (hb : d198467 q = 1) : d200911 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d200911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150145, d200911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150146 q = 1) (hb : d198467 q = 1) : d200912 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d200912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150146, d200912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro47231 (p : Pattern) (ha : d150152 p = 1) (hb : d198467 p = 1) : d200918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150147 q = 1) (hb : d198467 q = 1) : d200913 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d200913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150147, d200913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47230 q ha hb
  have h2 (q : Pattern) (ha : d150148 q = 1) (hb : d198467 q = 1) : d200914 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d200914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150148, d200914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150149 q = 1) (hb : d198467 q = 1) : d200915 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d200915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150149, d200915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150150 q = 1) (hb : d198467 q = 1) : d200916 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d200916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150150, d200916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150151 q = 1) (hb : d198467 q = 1) : d200917 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d200917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150151, d200917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150152 q = 1) (hb : d198467 q = 1) : d200918 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d200918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150152, d200918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47232 (p : Pattern) (ha : d13024 p = 1) (hb : d198467 p = 1) : d200932 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9795 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9795, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d9796 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9797 q = 1) (hb : d152852 q = 1) : d26105 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9797, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9798 q = 1) (hb : d152852 q = 1) : d26106 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9798, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13024 q = 1) (hb : d198467 q = 1) : d200932 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13024, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13024, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47233 (p : Pattern) (ha : d21736 p = 1) (hb : d198467 p = 1) : d200745 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d823 q = 1) : d823 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1089 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1090 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d829 q = 1) : d829 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d830 q = 1) (hb : d152852 q = 1) : d25761 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1091 q = 1) (hb : d152852 q = 1) : d25762 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1091, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1092 q = 1) (hb : d152852 q = 1) : d25763 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1092, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21736 q = 1) (hb : d198467 q = 1) : d200745 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21736, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21736, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47234 (p : Pattern) (ha : d21741 p = 1) (hb : d198467 p = 1) : d200921 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1096 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d538 q = 1) : d538 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d539 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1097 q = 1) (hb : d152852 q = 1) : d26087 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d26087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1097, d26087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1098 q = 1) (hb : d152852 q = 1) : d26088 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d26088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1098, d26088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21741 q = 1) (hb : d198467 q = 1) : d200921 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21741, d198467, d200921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21741, d198467, d200921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47235 (p : Pattern) (ha : d21747 p = 1) (hb : d198467 p = 1) : d200927 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9768 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9768, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9769 q = 1) (hb : d152852 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9769, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9770 q = 1) (hb : d152852 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9770, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21747 q = 1) (hb : d198467 q = 1) : d200927 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21747, d198467, d200927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21747, d198467, d200927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47236 (p : Pattern) (ha : d21753 p = 1) (hb : d198467 p = 1) : d200938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21737 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47233 q ha hb
    | true =>
      simp only [d21737, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21738 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21738, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21739 q = 1) (hb : d198467 q = 1) : d200748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21739, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21740 q = 1) (hb : d198467 q = 1) : d200749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21740, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21742 q = 1) (hb : d198467 q = 1) : d200922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47234 q ha hb
    | true =>
      simp only [d21742, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21743 q = 1) (hb : d198467 q = 1) : d200923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21743, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21744 q = 1) (hb : d198467 q = 1) : d200924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d200924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d200924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21745 q = 1) (hb : d198467 q = 1) : d200925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d200925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21745, d200925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21746 q = 1) (hb : d198467 q = 1) : d200926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21746, d200926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21746, d200926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21748 q = 1) (hb : d198467 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47235 q ha hb
    | true =>
      simp only [d21748, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21749 q = 1) (hb : d198467 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21749, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21750 q = 1) (hb : d198467 q = 1) : d200930 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21750, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21750, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21751 q = 1) (hb : d198467 q = 1) : d200931 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21751, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21751, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13025 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47232 q ha hb
    | true =>
      simp only [d13025, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d13026 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13026, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13027 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13028 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13028, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21752 q = 1) (hb : d198467 q = 1) : d200937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21752, d200937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21752, d200937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21753 q = 1) (hb : d198467 q = 1) : d200938 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21753, d200938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21753, d200938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47237 (p : Pattern) (ha : d21754 p = 1) (hb : d198467 p = 1) : d200932 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1106 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1107 q = 1) (hb : d152852 q = 1) : d26105 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1107, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1108 q = 1) (hb : d152852 q = 1) : d26106 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1108, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21754 q = 1) (hb : d198467 q = 1) : d200932 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21754, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21754, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47238 (p : Pattern) (ha : d21761 p = 1) (hb : d198467 p = 1) : d200941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21742 q = 1) (hb : d198467 q = 1) : d200922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47234 q ha hb
    | true =>
      simp only [d21742, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21743 q = 1) (hb : d198467 q = 1) : d200923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21743, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21744 q = 1) (hb : d198467 q = 1) : d200924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d200924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d200924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21745 q = 1) (hb : d198467 q = 1) : d200925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d200925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21745, d200925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21755 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47237 q ha hb
    | true =>
      simp only [d21755, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21756 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21756, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21757 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21758 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21758, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21759 q = 1) (hb : d198467 q = 1) : d200939 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21759, d200939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21759, d200939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13025 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47232 q ha hb
    | true =>
      simp only [d13025, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13026 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13026, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13027 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13028 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13028, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d21760 q = 1) (hb : d198467 q = 1) : d200940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21760, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21760, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21761 q = 1) (hb : d198467 q = 1) : d200941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21761, d200941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21761, d200941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47239 (p : Pattern) (ha : d21765 p = 1) (hb : d198467 p = 1) : d200932 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5014 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5014, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5014, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d5015 q = 1) (hb : d152852 q = 1) : d26105 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5015, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5015, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5016 q = 1) (hb : d152852 q = 1) : d26106 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5016, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5016, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21765 q = 1) (hb : d198467 q = 1) : d200932 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21765, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21765, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47240 (p : Pattern) (ha : d21771 p = 1) (hb : d198467 p = 1) : d200945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21766 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21766, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47239 q ha hb
    | true =>
      simp only [d21766, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21767 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21767, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21767, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21768 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21768, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21768, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21769 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21769, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21769, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21770 q = 1) (hb : d198467 q = 1) : d200940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21770, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21770, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d198467 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21771 q = 1) (hb : d198467 q = 1) : d200945 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21771, d200945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21771, d200945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47241 (p : Pattern) (ha : d21777 p = 1) (hb : d198467 p = 1) : d200945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21755 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47237 q ha hb
    | true =>
      simp only [d21755, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21756 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21756, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21757 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21758 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21758, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21776 q = 1) (hb : d198467 q = 1) : d200940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21776, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21776, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d198467 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21777 q = 1) (hb : d198467 q = 1) : d200945 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21777, d200945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21777, d200945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47242 (p : Pattern) (ha : d21783 p = 1) (hb : d198467 p = 1) : d200952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d198467 q = 1) : d200942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47236 q ha hb
    | true =>
      simp only [d21762, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47238 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d198467 q = 1) : d200943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d198467 q = 1) : d200944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21772 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47238 q ha hb
    | true =>
      simp only [d21772, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47240 q ha hb
  have h5 (q : Pattern) (ha : d21773 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21774 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21775 q = 1) (hb : d198467 q = 1) : d200949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21778 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47238 q ha hb
    | true =>
      simp only [d21778, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47241 q ha hb
  have h9 (q : Pattern) (ha : d21779 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21780 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21781 q = 1) (hb : d198467 q = 1) : d200950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21781, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21782 q = 1) (hb : d198467 q = 1) : d200951 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21782, d200951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21782, d200951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21783 q = 1) (hb : d198467 q = 1) : d200952 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21783, d200952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21783, d200952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro47243 (p : Pattern) (ha : d21787 p = 1) (hb : d198467 p = 1) : d200956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21778 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47238 q ha hb
    | true =>
      simp only [d21778, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47241 q ha hb
  have h2 (q : Pattern) (ha : d21779 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21780 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21781 q = 1) (hb : d198467 q = 1) : d200950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21781, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21786 q = 1) (hb : d198467 q = 1) : d200955 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21786, d200955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21786, d200955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21787 q = 1) (hb : d198467 q = 1) : d200956 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21787, d200956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21787, d200956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47244 (p : Pattern) (ha : d21793 p = 1) (hb : d198467 p = 1) : d200962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47242 q ha hb
    | true =>
      simp only [d21784, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47243 q ha hb
    | true =>
      simp only [d21788, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d198467 q = 1) : d200960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d198467 q = 1) : d200961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21793 q = 1) (hb : d198467 q = 1) : d200962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21793, d200962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21793, d200962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47245 (p : Pattern) (ha : d21797 p = 1) (hb : d198467 p = 1) : d200966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47243 q ha hb
    | true =>
      simp only [d21788, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d198467 q = 1) : d200963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d198467 q = 1) : d200964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d198467 q = 1) : d200965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d200965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d200965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21797 q = 1) (hb : d198467 q = 1) : d200966 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21797, d200966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21797, d200966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47246 (p : Pattern) (ha : d21803 p = 1) (hb : d198467 p = 1) : d200972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d198467 q = 1) : d200967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47244 q ha hb
    | true =>
      simp only [d21798, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47245 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d198467 q = 1) : d200968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d198467 q = 1) : d200969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d198467 q = 1) : d200970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d198467 q = 1) : d200971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21803 q = 1) (hb : d198467 q = 1) : d200972 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47247 (p : Pattern) (ha : d21806 p = 1) (hb : d198467 p = 1) : d200975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47242 q ha hb
    | true =>
      simp only [d21784, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47243 q ha hb
    | true =>
      simp only [d21788, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d198467 q = 1) : d200960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d198467 q = 1) : d200961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21806 q = 1) (hb : d198467 q = 1) : d200975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21806, d200975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21806, d200975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47248 (p : Pattern) (ha : d21807 p = 1) (hb : d198467 p = 1) : d200976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47243 q ha hb
    | true =>
      simp only [d21788, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d198467 q = 1) : d200963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d198467 q = 1) : d200964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d198467 q = 1) : d200965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d200965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d200965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21807 q = 1) (hb : d198467 q = 1) : d200976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21807, d200976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21807, d200976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47249 (p : Pattern) (ha : d21813 p = 1) (hb : d198467 p = 1) : d200982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d198467 q = 1) : d200967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47244 q ha hb
    | true =>
      simp only [d21798, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47245 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d198467 q = 1) : d200968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d198467 q = 1) : d200969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d198467 q = 1) : d200970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d198467 q = 1) : d200971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21808 q = 1) (hb : d198467 q = 1) : d200977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47247 q ha hb
    | true =>
      simp only [d21808, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47248 q ha hb
  have h7 (q : Pattern) (ha : d21809 q = 1) (hb : d198467 q = 1) : d200978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21810 q = 1) (hb : d198467 q = 1) : d200979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21810, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21811 q = 1) (hb : d198467 q = 1) : d200980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21812 q = 1) (hb : d198467 q = 1) : d200981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21813 q = 1) (hb : d198467 q = 1) : d200982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21813, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
end NetHack.Soko22Hazard87
