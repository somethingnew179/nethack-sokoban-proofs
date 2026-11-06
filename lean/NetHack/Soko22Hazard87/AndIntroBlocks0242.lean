import NetHack.Soko22Hazard87.AndIntroBlocks0241
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro60500 (p : Pattern) (ha : d208035 p = 1) (hb : d231266 p = 1) : d210968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23994 q = 1) (hb : d208035 q = 1) : d210179 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23994, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59992 q ha hb
    | true =>
      simp only [d23994, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59995 q ha hb
  have h2 (q : Pattern) (ha : d23995 q = 1) (hb : d208035 q = 1) : d210180 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23995, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23995, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231247 q = 1) : d210949 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231247, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231247, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231248 q = 1) : d210950 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231248, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231248, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231250 q = 1) : d210952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231250, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231250, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60498 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231251 q = 1) : d210953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231251, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231251, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d231252 q = 1) : d210954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231252, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231252, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d231253 q = 1) : d210955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231253, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231253, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d231254 q = 1) : d210956 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231254, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231254, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d231261 q = 1) : d210963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231261, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231261, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60499 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d231262 q = 1) : d210964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231262, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231262, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d231263 q = 1) : d210965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231263, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231263, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d231264 q = 1) : d210966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231264, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231264, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d231265 q = 1) : d210967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231265, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231265, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d231266 q = 1) : d210968 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231266, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231266, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60501 (p : Pattern) (ha : d208035 p = 1) (hb : d231272 p = 1) : d210974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231267 q = 1) : d210969 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231267, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231267, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60500 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231268 q = 1) : d210970 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231268, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231268, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231269 q = 1) : d210971 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231269, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231269, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231270 q = 1) : d210972 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231270, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231270, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231271 q = 1) : d210973 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231271, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231271, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231272 q = 1) : d210974 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231272, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231272, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60502 (p : Pattern) (ha : d208035 p = 1) (hb : d231278 p = 1) : d210980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24370 q = 1) (hb : d208035 q = 1) : d210416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24370, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60050 q ha hb
    | true =>
      simp only [d24370, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60051 q ha hb
  have h2 (q : Pattern) (ha : d24371 q = 1) (hb : d208035 q = 1) : d210417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24371, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24372 q = 1) (hb : d208035 q = 1) : d210418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24372, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24373 q = 1) (hb : d208035 q = 1) : d210419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24373, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24374 q = 1) (hb : d208035 q = 1) : d210420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24374, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231278 q = 1) : d210980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231278, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231278, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro60503 (p : Pattern) (ha : d208035 p = 1) (hb : d231289 p = 1) : d210991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231284 q = 1) : d210986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231284, d210986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60088 q hb ha
    | true =>
      simp only [d231284, d210986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60059 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231285 q = 1) : d210987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231285, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231285, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231286 q = 1) : d210988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231286, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231286, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231287 q = 1) : d210989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231287, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231287, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231288 q = 1) : d210990 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231288, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231288, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231289 q = 1) : d210991 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231289, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231289, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60504 (p : Pattern) (ha : d208035 p = 1) (hb : d231295 p = 1) : d210997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24376 q = 1) (hb : d208035 q = 1) : d210422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60049 q ha hb
    | true =>
      simp only [d24376, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60052 q ha hb
  have h2 (q : Pattern) (ha : d24377 q = 1) (hb : d208035 q = 1) : d210423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24377, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231276 q = 1) : d210978 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231276, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231276, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231277 q = 1) : d210979 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231277, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231277, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231279 q = 1) : d210981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231279, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231279, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60502 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231280 q = 1) : d210982 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231280, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231280, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d231281 q = 1) : d210983 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231281, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231281, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d231282 q = 1) : d210984 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231282, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231282, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d231283 q = 1) : d210985 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231283, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231283, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d231290 q = 1) : d210992 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231290, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231290, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60503 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d231291 q = 1) : d210993 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231291, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231291, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d231292 q = 1) : d210994 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231292, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231292, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d231293 q = 1) : d210995 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231293, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231293, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d231294 q = 1) : d210996 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231294, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231294, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d231295 q = 1) : d210997 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231295, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231295, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60505 (p : Pattern) (ha : d208035 p = 1) (hb : d231301 p = 1) : d211003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231296 q = 1) : d210998 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231296, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231296, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60504 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231297 q = 1) : d210999 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231297, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231297, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231298 q = 1) : d211000 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231298, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231298, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231299 q = 1) : d211001 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231299, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231299, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231300 q = 1) : d211002 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231300, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231300, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231301 q = 1) : d211003 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231301, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231301, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60506 (p : Pattern) (ha : d208035 p = 1) (hb : d231308 p = 1) : d211010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24751 q = 1) (hb : d208035 q = 1) : d210648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24751, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60107 q ha hb
    | true =>
      simp only [d24751, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60108 q ha hb
  have h2 (q : Pattern) (ha : d24752 q = 1) (hb : d208035 q = 1) : d210649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24752, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24753 q = 1) (hb : d208035 q = 1) : d210650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24753, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24754 q = 1) (hb : d208035 q = 1) : d210651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24754, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24755 q = 1) (hb : d208035 q = 1) : d210652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24755, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231308 q = 1) : d211010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231308, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231308, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro60507 (p : Pattern) (ha : d208035 p = 1) (hb : d231319 p = 1) : d211021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231314 q = 1) : d211016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231314, d211016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60145 q hb ha
    | true =>
      simp only [d231314, d211016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60116 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231315 q = 1) : d211017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231315, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231315, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231316 q = 1) : d211018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231316, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231316, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231317 q = 1) : d211019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231317, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231317, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231318 q = 1) : d211020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231318, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231318, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231319 q = 1) : d211021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231319, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231319, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60508 (p : Pattern) (ha : d208035 p = 1) (hb : d231325 p = 1) : d211027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24757 q = 1) (hb : d208035 q = 1) : d210654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24757, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60106 q ha hb
    | true =>
      simp only [d24757, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60109 q ha hb
  have h2 (q : Pattern) (ha : d24758 q = 1) (hb : d208035 q = 1) : d210655 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24758, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24758, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231306 q = 1) : d211008 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231306, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231306, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231307 q = 1) : d211009 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231307, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231307, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231309 q = 1) : d211011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231309, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231309, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60506 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231310 q = 1) : d211012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231310, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231310, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d231311 q = 1) : d211013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231311, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231311, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d231312 q = 1) : d211014 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231312, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231312, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d231313 q = 1) : d211015 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231313, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231313, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d231320 q = 1) : d211022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231320, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231320, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60507 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d231321 q = 1) : d211023 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231321, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231321, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d231322 q = 1) : d211024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231322, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231322, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d231323 q = 1) : d211025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231323, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231323, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d231324 q = 1) : d211026 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231324, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231324, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d231325 q = 1) : d211027 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231325, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231325, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60509 (p : Pattern) (ha : d208035 p = 1) (hb : d231331 p = 1) : d211033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231326 q = 1) : d211028 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231326, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231326, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60508 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231327 q = 1) : d211029 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231327, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231327, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231328 q = 1) : d211030 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231328, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231328, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231329 q = 1) : d211031 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231329, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231329, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231330 q = 1) : d211032 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231330, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231330, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231331 q = 1) : d211033 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231331, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231331, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60510 (p : Pattern) (ha : d208035 p = 1) (hb : d231337 p = 1) : d211039 p = 1 := by
  have h0 (q : Pattern) (ha : d208035 q = 1) (hb : d231218 q = 1) : d210920 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231218, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60489 q ha hb
    | true =>
      simp only [d231218, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60493 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231245 q = 1) : d210947 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231245, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231245, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60497 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231246 q = 1) : d210948 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231246, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231246, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231273 q = 1) : d210975 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231273, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231273, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60501 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231274 q = 1) : d210976 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231274, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231274, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231275 q = 1) : d210977 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231275, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231275, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d231302 q = 1) : d211004 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231302, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231302, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60505 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d231303 q = 1) : d211005 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231303, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231303, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d231304 q = 1) : d211006 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231304, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231304, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d231305 q = 1) : d211007 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d231305, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231305, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d231332 q = 1) : d211034 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231332, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231332, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60509 q ha hb
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d231333 q = 1) : d211035 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231333, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231333, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d231334 q = 1) : d211036 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231334, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231334, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d231335 q = 1) : d211037 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d231335, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231335, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d231336 q = 1) : d211038 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d231336, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231336, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d208035 q = 1) (hb : d231337 q = 1) : d211039 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d231337, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d231337, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro60511 (p : Pattern) (ha : d208035 p = 1) (hb : d231343 p = 1) : d211045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231338 q = 1) : d211040 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d231338, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60510 q ha hb
    | true =>
      simp only [d231338, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231339 q = 1) : d211041 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d231339, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231339, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231340 q = 1) : d211042 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d231340, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231340, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231341 q = 1) : d211043 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d231341, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231341, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231342 q = 1) : d211044 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d231342, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231342, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231343 q = 1) : d211045 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d231343, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231343, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60512 (p : Pattern) (ha : d208035 p = 1) (hb : d231349 p = 1) : d211051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231344 q = 1) : d211046 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d231344, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60511 q ha hb
    | true =>
      simp only [d231344, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231345 q = 1) : d211047 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d231345, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231345, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231346 q = 1) : d211048 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d231346, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231346, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231347 q = 1) : d211049 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d231347, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231347, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231348 q = 1) : d211050 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d231348, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231348, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231349 q = 1) : d211051 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d231349, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231349, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60513 (p : Pattern) (ha : d208035 p = 1) (hb : d231355 p = 1) : d211057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231350 q = 1) : d211052 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d231350, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60512 q ha hb
    | true =>
      simp only [d231350, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231351 q = 1) : d211053 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d231351, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231351, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231352 q = 1) : d211054 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d231352, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231352, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231353 q = 1) : d211055 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d231353, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231353, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231354 q = 1) : d211056 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d231354, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231354, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231355 q = 1) : d211057 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d231355, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231355, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60514 (p : Pattern) (ha : d208035 p = 1) (hb : d231361 p = 1) : d211063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231356 q = 1) : d211058 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d231356, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60513 q ha hb
    | true =>
      simp only [d231356, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231357 q = 1) : d211059 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d231357, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231357, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231358 q = 1) : d211060 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d231358, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231358, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231359 q = 1) : d211061 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d231359, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231359, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231360 q = 1) : d211062 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d231360, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231360, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231361 q = 1) : d211063 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d231361, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231361, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60515 (p : Pattern) (ha : d208035 p = 1) (hb : d231367 p = 1) : d211069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231362 q = 1) : d211064 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d231362, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60514 q ha hb
    | true =>
      simp only [d231362, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231363 q = 1) : d211065 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d231363, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231363, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231364 q = 1) : d211066 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d231364, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231364, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231365 q = 1) : d211067 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d231365, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231365, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231366 q = 1) : d211068 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d231366, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231366, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231367 q = 1) : d211069 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d231367, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231367, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60516 (p : Pattern) (ha : d208035 p = 1) (hb : d231373 p = 1) : d211075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231368 q = 1) : d211070 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d231368, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60515 q ha hb
    | true =>
      simp only [d231368, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231369 q = 1) : d211071 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d231369, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231369, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231370 q = 1) : d211072 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d231370, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231370, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231371 q = 1) : d211073 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d231371, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231371, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231372 q = 1) : d211074 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d231372, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231372, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231373 q = 1) : d211075 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d231373, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231373, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60517 (p : Pattern) (ha : d208035 p = 1) (hb : d231379 p = 1) : d211081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d231374 q = 1) : d211076 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d231374, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60516 q ha hb
    | true =>
      simp only [d231374, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d231375 q = 1) : d211077 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d231375, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231375, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d231376 q = 1) : d211078 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d231376, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231376, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d231377 q = 1) : d211079 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d231377, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231377, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d231378 q = 1) : d211080 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d231378, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231378, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d231379 q = 1) : d211081 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d231379, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231379, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60518 (p : Pattern) (ha : d146966 p = 1) (hb : d209612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d146852 q = 1) (hb : d209554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60164 q ha hb
    | true =>
      simp only [d146852, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d146956 q = 1) (hb : d209608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d146956, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146963 q = 1) (hb : d209609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146964 q = 1) (hb : d209610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146965 q = 1) (hb : d209611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146966 q = 1) (hb : d209612 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146966, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146966, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60519 (p : Pattern) (ha : d146985 p = 1) (hb : d209619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146852 q = 1) (hb : d209554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60164 q ha hb
    | true =>
      simp only [d146852, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d146956 q = 1) (hb : d209608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146956, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d146963 q = 1) (hb : d209609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146964 q = 1) (hb : d209610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146965 q = 1) (hb : d209611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d146975 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d146859 q = 1) (hb : d209561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60166 q ha hb
    | true =>
      simp only [d146859, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d146978 q = 1) (hb : d209615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d146978, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146982 q = 1) (hb : d209616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146982, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d146983 q = 1) (hb : d209617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146983, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d146983, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146984 q = 1) (hb : d209618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146984, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d146984, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146985 q = 1) (hb : d209619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146985, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146985, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60520 (p : Pattern) (ha : d146994 p = 1) (hb : d210871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146859 q = 1) (hb : d209561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60166 q ha hb
    | true =>
      simp only [d146859, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d146978 q = 1) (hb : d209615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146978, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146982 q = 1) (hb : d209616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146982, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146992 q = 1) (hb : d209617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146992, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146992, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146993 q = 1) (hb : d209618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146993, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146993, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146994 q = 1) (hb : d210871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146994, d210871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146994, d210871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60521 (p : Pattern) (ha : d147030 p = 1) (hb : d210881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146891 q = 1) (hb : d209591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146891, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60171 q ha hb
    | true =>
      simp only [d146891, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d147020 q = 1) (hb : d210877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147020, d210877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147020, d210877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147027 q = 1) (hb : d210878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147027, d210878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147027, d210878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147028 q = 1) (hb : d210879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147028, d210879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147028, d210879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147029 q = 1) (hb : d210880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147029, d210880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147029, d210880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147030 q = 1) (hb : d210881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147030, d210881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147030, d210881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60522 (p : Pattern) (ha : d147036 p = 1) (hb : d210887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146922 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146986 q = 1) (hb : d209620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146986, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60518 q ha hb
    | true =>
      simp only [d146986, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60519 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146989 q = 1) (hb : d209621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146989, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146989, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146990 q = 1) (hb : d210869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146990, d210869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146990, d210869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146991 q = 1) (hb : d210870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146991, d210870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146991, d210870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146995 q = 1) (hb : d210872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146995, d210872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146995, d210872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60520 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146996 q = 1) (hb : d210873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146996, d210873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146996, d210873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146997 q = 1) (hb : d210874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146997, d210874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146997, d210874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d146998 q = 1) (hb : d210875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146998, d210875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146998, d210875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d146999 q = 1) (hb : d210876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146999, d210876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146999, d210876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147031 q = 1) (hb : d210882 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147031, d210882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147031, d210882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60521 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147032 q = 1) (hb : d210883 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147032, d210883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147032, d210883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147033 q = 1) (hb : d210884 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147033, d210884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147033, d210884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147034 q = 1) (hb : d210885 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147034, d210885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147034, d210885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147035 q = 1) (hb : d210886 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147035, d210886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147035, d210886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147036 q = 1) (hb : d210887 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147036, d210887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147036, d210887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60523 (p : Pattern) (ha : d147042 p = 1) (hb : d210893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d146903 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28391 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d146904 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d146905 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d146906 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d146907 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147037 q = 1) (hb : d210888 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147037, d210888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147037, d210888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60522 q ha hb
  have h8 (q : Pattern) (ha : d147038 q = 1) (hb : d210889 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147038, d210889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147038, d210889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147039 q = 1) (hb : d210890 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147039, d210890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147039, d210890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147040 q = 1) (hb : d210891 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147040, d210891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147040, d210891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147041 q = 1) (hb : d210892 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147041, d210892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147041, d210892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147042 q = 1) (hb : d210893 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147042, d210893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147042, d210893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro60524 (p : Pattern) (ha : d147136 p = 1) (hb : d209752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147060 q = 1) (hb : d209747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60200 q ha hb
    | true =>
      simp only [d147060, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60201 q ha hb
  have h5 (q : Pattern) (ha : d147126 q = 1) (hb : d209748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147126, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147133 q = 1) (hb : d209749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147133, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147134 q = 1) (hb : d209750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147134, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147135 q = 1) (hb : d209751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147135, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147136 q = 1) (hb : d209752 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147136, d209752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147136, d209752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60525 (p : Pattern) (ha : d147157 p = 1) (hb : d209762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147060 q = 1) (hb : d209747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60200 q ha hb
    | true =>
      simp only [d147060, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60201 q ha hb
  have h4 (q : Pattern) (ha : d147126 q = 1) (hb : d209748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147126, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147133 q = 1) (hb : d209749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147133, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147134 q = 1) (hb : d209750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147134, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147135 q = 1) (hb : d209751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147135, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147142 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147147 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147070 q = 1) (hb : d209757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60203 q ha hb
    | true =>
      simp only [d147070, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60204 q ha hb
  have h13 (q : Pattern) (ha : d147150 q = 1) (hb : d209758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147150, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147154 q = 1) (hb : d209759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147154, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147155 q = 1) (hb : d209760 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147155, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147155, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147156 q = 1) (hb : d209761 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147156, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147156, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147157 q = 1) (hb : d209762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147157, d209762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147157, d209762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60526 (p : Pattern) (ha : d147177 p = 1) (hb : d210896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147070 q = 1) (hb : d209757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60203 q ha hb
    | true =>
      simp only [d147070, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60204 q ha hb
  have h3 (q : Pattern) (ha : d147150 q = 1) (hb : d209758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147150, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147154 q = 1) (hb : d209759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147154, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147175 q = 1) (hb : d209760 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147175, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147175, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147176 q = 1) (hb : d209761 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147176, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147176, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147177 q = 1) (hb : d210896 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147177, d210896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147177, d210896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60527 (p : Pattern) (ha : d147241 p = 1) (hb : d210907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147230 q = 1) (hb : d210902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147230, d210902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60235 q ha hb
    | true =>
      simp only [d147230, d210902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60238 q ha hb
  have h3 (q : Pattern) (ha : d147231 q = 1) (hb : d210903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147231, d210903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147231, d210903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147237 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147238 q = 1) (hb : d210904 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147238, d210904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147238, d210904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147239 q = 1) (hb : d210905 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147239, d210905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147239, d210905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147240 q = 1) (hb : d210906 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147240, d210906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147240, d210906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147241 q = 1) (hb : d210907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147241, d210907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147241, d210907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60528 (p : Pattern) (ha : d147254 p = 1) (hb : d210913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147158 q = 1) (hb : d209763 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147158, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60524 q ha hb
    | true =>
      simp only [d147158, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60525 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147172 q = 1) (hb : d209764 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147172, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147172, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147173 q = 1) (hb : d210894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147173, d210894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147173, d210894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147174 q = 1) (hb : d210895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147174, d210895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147174, d210895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147178 q = 1) (hb : d210897 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147178, d210897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147178, d210897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60526 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147180 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147181 q = 1) (hb : d210898 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147181, d210898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147181, d210898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147182 q = 1) (hb : d210899 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147182, d210899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147182, d210899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147183 q = 1) (hb : d210900 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147183, d210900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147183, d210900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147184 q = 1) (hb : d210901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147184, d210901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147184, d210901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147242 q = 1) (hb : d210908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147242, d210908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147242, d210908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60527 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147250 q = 1) (hb : d210909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147250, d210909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147250, d210909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147251 q = 1) (hb : d210910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147251, d210910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147251, d210910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147252 q = 1) (hb : d210911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147252, d210911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147252, d210911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147253 q = 1) (hb : d210912 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147253, d210912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147253, d210912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147254 q = 1) (hb : d210913 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147254, d210913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147254, d210913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60529 (p : Pattern) (ha : d147260 p = 1) (hb : d210919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147255 q = 1) (hb : d210914 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147255, d210914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147255, d210914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60528 q ha hb
  have h2 (q : Pattern) (ha : d147256 q = 1) (hb : d210915 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147256, d210915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147256, d210915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147257 q = 1) (hb : d210916 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147257, d210916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147257, d210916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147258 q = 1) (hb : d210917 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147258, d210917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147258, d210917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147259 q = 1) (hb : d210918 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147259, d210918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147259, d210918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147260 q = 1) (hb : d210919 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147260, d210919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147260, d210919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60530 (p : Pattern) (ha : d147365 p = 1) (hb : d209950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147289 q = 1) (hb : d209945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60247 q ha hb
    | true =>
      simp only [d147289, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60248 q ha hb
  have h5 (q : Pattern) (ha : d147355 q = 1) (hb : d209946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147355, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147362 q = 1) (hb : d209947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147362, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147363 q = 1) (hb : d209948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147363, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147364 q = 1) (hb : d209949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147364, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147365 q = 1) (hb : d209950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147365, d209950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147365, d209950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60531 (p : Pattern) (ha : d147386 p = 1) (hb : d209960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147289 q = 1) (hb : d209945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60247 q ha hb
    | true =>
      simp only [d147289, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60248 q ha hb
  have h4 (q : Pattern) (ha : d147355 q = 1) (hb : d209946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147355, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147362 q = 1) (hb : d209947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147362, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147363 q = 1) (hb : d209948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147363, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147364 q = 1) (hb : d209949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147364, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147376 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147299 q = 1) (hb : d209955 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60250 q ha hb
    | true =>
      simp only [d147299, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60251 q ha hb
  have h13 (q : Pattern) (ha : d147379 q = 1) (hb : d209956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147379, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147383 q = 1) (hb : d209957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147383, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147384 q = 1) (hb : d209958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147384, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147384, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147385 q = 1) (hb : d209959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147385, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147385, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147386 q = 1) (hb : d209960 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147386, d209960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147386, d209960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60532 (p : Pattern) (ha : d147406 p = 1) (hb : d210923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147299 q = 1) (hb : d209955 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60250 q ha hb
    | true =>
      simp only [d147299, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60251 q ha hb
  have h3 (q : Pattern) (ha : d147379 q = 1) (hb : d209956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147379, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147383 q = 1) (hb : d209957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147383, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147404 q = 1) (hb : d209958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147404, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147404, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147405 q = 1) (hb : d209959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147405, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147405, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147406 q = 1) (hb : d210923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147406, d210923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147406, d210923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60533 (p : Pattern) (ha : d147480 p = 1) (hb : d210934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147464 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147469 q = 1) (hb : d210929 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147469, d210929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60285 q ha hb
    | true =>
      simp only [d147469, d210929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60288 q ha hb
  have h3 (q : Pattern) (ha : d147470 q = 1) (hb : d210930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147470, d210930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147470, d210930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147477 q = 1) (hb : d210931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147477, d210931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147477, d210931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147478 q = 1) (hb : d210932 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147478, d210932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147478, d210932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147479 q = 1) (hb : d210933 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147479, d210933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147479, d210933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147480 q = 1) (hb : d210934 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147480, d210934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147480, d210934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60534 (p : Pattern) (ha : d147493 p = 1) (hb : d210940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147387 q = 1) (hb : d209961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147387, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60530 q ha hb
    | true =>
      simp only [d147387, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60531 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147401 q = 1) (hb : d209962 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147401, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147401, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147402 q = 1) (hb : d210921 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147402, d210921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147402, d210921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147403 q = 1) (hb : d210922 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147403, d210922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147403, d210922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147407 q = 1) (hb : d210924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147407, d210924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147407, d210924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60532 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147409 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147410 q = 1) (hb : d210925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147410, d210925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147410, d210925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147411 q = 1) (hb : d210926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147411, d210926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147411, d210926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147412 q = 1) (hb : d210927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147412, d210927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147412, d210927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147413 q = 1) (hb : d210928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147413, d210928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147413, d210928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147481 q = 1) (hb : d210935 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147481, d210935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147481, d210935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60533 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147489 q = 1) (hb : d210936 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147489, d210936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147489, d210936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147490 q = 1) (hb : d210937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147490, d210937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147490, d210937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147491 q = 1) (hb : d210938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147491, d210938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147491, d210938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147492 q = 1) (hb : d210939 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147492, d210939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147492, d210939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147493 q = 1) (hb : d210940 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147493, d210940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147493, d210940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60535 (p : Pattern) (ha : d147499 p = 1) (hb : d210946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147494 q = 1) (hb : d210941 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147494, d210941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147494, d210941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60534 q ha hb
  have h2 (q : Pattern) (ha : d147495 q = 1) (hb : d210942 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147495, d210942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147495, d210942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147496 q = 1) (hb : d210943 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147496, d210943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147496, d210943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147497 q = 1) (hb : d210944 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147497, d210944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147497, d210944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147498 q = 1) (hb : d210945 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147498, d210945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147498, d210945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147499 q = 1) (hb : d210946 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147499, d210946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147499, d210946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60536 (p : Pattern) (ha : d147664 p = 1) (hb : d210168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147564 q = 1) (hb : d210163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60304 q ha hb
    | true =>
      simp only [d147564, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60305 q ha hb
  have h5 (q : Pattern) (ha : d147645 q = 1) (hb : d210164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147645, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147661 q = 1) (hb : d210165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147661, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147662 q = 1) (hb : d210166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147662, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147663 q = 1) (hb : d210167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147663, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147664 q = 1) (hb : d210168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147664, d210168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147664, d210168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60537 (p : Pattern) (ha : d147686 p = 1) (hb : d210178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147564 q = 1) (hb : d210163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60304 q ha hb
    | true =>
      simp only [d147564, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60305 q ha hb
  have h4 (q : Pattern) (ha : d147645 q = 1) (hb : d210164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147645, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147661 q = 1) (hb : d210165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147661, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147662 q = 1) (hb : d210166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147662, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147663 q = 1) (hb : d210167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147663, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147670 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147675 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147574 q = 1) (hb : d210173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60307 q ha hb
    | true =>
      simp only [d147574, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60308 q ha hb
  have h13 (q : Pattern) (ha : d147679 q = 1) (hb : d210174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147679, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147683 q = 1) (hb : d210175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147683, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147684 q = 1) (hb : d210176 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147684, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147684, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147685 q = 1) (hb : d210177 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147685, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147685, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147686 q = 1) (hb : d210178 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147686, d210178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147686, d210178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60538 (p : Pattern) (ha : d147711 p = 1) (hb : d210951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147574 q = 1) (hb : d210173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60307 q ha hb
    | true =>
      simp only [d147574, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60308 q ha hb
  have h3 (q : Pattern) (ha : d147679 q = 1) (hb : d210174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147679, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147683 q = 1) (hb : d210175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147683, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147709 q = 1) (hb : d210176 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147709, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147709, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147710 q = 1) (hb : d210177 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147710, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147710, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147711 q = 1) (hb : d210951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147711, d210951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147711, d210951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60539 (p : Pattern) (ha : d147807 p = 1) (hb : d210310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147765 q = 1) (hb : d210295 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d210295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60339 q ha hb
    | true =>
      simp only [d147765, d210295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60341 q ha hb
  have h2 (q : Pattern) (ha : d147766 q = 1) (hb : d210296 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d210296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d210296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147767 q = 1) (hb : d210297 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d210297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d210297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147774 q = 1) (hb : d210300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d210300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60341 q ha hb
    | true =>
      simp only [d147774, d210300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60342 q ha hb
  have h5 (q : Pattern) (ha : d147775 q = 1) (hb : d210301 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d210301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d210301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147776 q = 1) (hb : d210302 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d210302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d210302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147777 q = 1) (hb : d210303 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d210303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147777, d210303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147793 q = 1) (hb : d210300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147793, d210300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60341 q ha hb
    | true =>
      simp only [d147793, d210300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60346 q ha hb
  have h9 (q : Pattern) (ha : d147794 q = 1) (hb : d210301 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147794, d210301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147794, d210301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147795 q = 1) (hb : d210302 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147795, d210302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147795, d210302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147796 q = 1) (hb : d210308 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147796, d210308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147796, d210308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147806 q = 1) (hb : d210309 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147806, d210309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147806, d210309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147807 q = 1) (hb : d210310 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147807, d210310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147807, d210310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro60540 (p : Pattern) (ha : d147813 p = 1) (hb : d210324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147808 q = 1) (hb : d210311 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147808, d210311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60539 q ha hb
    | true =>
      simp only [d147808, d210311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147809 q = 1) (hb : d210312 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147809, d210312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147809, d210312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147799 q = 1) (hb : d210319 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d210319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60347 q ha hb
    | true =>
      simp only [d147799, d210319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147800 q = 1) (hb : d210320 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d210320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d210320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147810 q = 1) (hb : d210321 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147810, d210321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147810, d210321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147811 q = 1) (hb : d210322 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147811, d210322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147811, d210322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147812 q = 1) (hb : d210323 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147812, d210323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147812, d210323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147813 q = 1) (hb : d210324 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147813, d210324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147813, d210324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro60541 (p : Pattern) (ha : d147838 p = 1) (hb : d210962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147818 q = 1) (hb : d210957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147818, d210957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60540 q ha hb
    | true =>
      simp only [d147818, d210957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60353 q ha hb
  have h3 (q : Pattern) (ha : d147819 q = 1) (hb : d210958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147819, d210958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147819, d210958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147835 q = 1) (hb : d210959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147835, d210959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147835, d210959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147836 q = 1) (hb : d210960 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147836, d210960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147836, d210960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147837 q = 1) (hb : d210961 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147837, d210961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147837, d210961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147838 q = 1) (hb : d210962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147838, d210962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147838, d210962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60542 (p : Pattern) (ha : d147851 p = 1) (hb : d210968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147687 q = 1) (hb : d210179 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147687, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60536 q ha hb
    | true =>
      simp only [d147687, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60537 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147706 q = 1) (hb : d210180 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147706, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147706, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147707 q = 1) (hb : d210949 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147707, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147707, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147708 q = 1) (hb : d210950 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147708, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147708, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147712 q = 1) (hb : d210952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147712, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147712, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60538 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147715 q = 1) (hb : d210953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147715, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147715, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147716 q = 1) (hb : d210954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147716, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147716, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147717 q = 1) (hb : d210955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147717, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147717, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147718 q = 1) (hb : d210956 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147718, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147718, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147839 q = 1) (hb : d210963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147839, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147839, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60541 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147847 q = 1) (hb : d210964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147847, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147847, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147848 q = 1) (hb : d210965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147848, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147848, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147849 q = 1) (hb : d210966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147849, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147849, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147850 q = 1) (hb : d210967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147850, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147850, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147851 q = 1) (hb : d210968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147851, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147851, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60543 (p : Pattern) (ha : d147857 p = 1) (hb : d210974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147852 q = 1) (hb : d210969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147852, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147852, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60542 q ha hb
  have h2 (q : Pattern) (ha : d147853 q = 1) (hb : d210970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147853, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147853, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147854 q = 1) (hb : d210971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147854, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147854, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147855 q = 1) (hb : d210972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147855, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147855, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147856 q = 1) (hb : d210973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147856, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147856, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147857 q = 1) (hb : d210974 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147857, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147857, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60544 (p : Pattern) (ha : d148013 p = 1) (hb : d210411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147918 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60368 q ha hb
    | true =>
      simp only [d147918, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60369 q ha hb
  have h5 (q : Pattern) (ha : d147994 q = 1) (hb : d210407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147994, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148010 q = 1) (hb : d210408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148010, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148011 q = 1) (hb : d210409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148011, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148012 q = 1) (hb : d210410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148012, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148013 q = 1) (hb : d210411 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148013, d210411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148013, d210411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60545 (p : Pattern) (ha : d148035 p = 1) (hb : d210421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147918 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60368 q ha hb
    | true =>
      simp only [d147918, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60369 q ha hb
  have h4 (q : Pattern) (ha : d147994 q = 1) (hb : d210407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147994, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148010 q = 1) (hb : d210408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148010, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148011 q = 1) (hb : d210409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148011, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148012 q = 1) (hb : d210410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148012, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148019 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147928 q = 1) (hb : d210416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60371 q ha hb
    | true =>
      simp only [d147928, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60372 q ha hb
  have h13 (q : Pattern) (ha : d148028 q = 1) (hb : d210417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148028, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148032 q = 1) (hb : d210418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148032, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148033 q = 1) (hb : d210419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148033, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148033, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148034 q = 1) (hb : d210420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148034, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148034, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148035 q = 1) (hb : d210421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148035, d210421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148035, d210421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60546 (p : Pattern) (ha : d148060 p = 1) (hb : d210980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147928 q = 1) (hb : d210416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60371 q ha hb
    | true =>
      simp only [d147928, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60372 q ha hb
  have h3 (q : Pattern) (ha : d148028 q = 1) (hb : d210417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148028, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148032 q = 1) (hb : d210418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148032, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148058 q = 1) (hb : d210419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148058, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148058, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148059 q = 1) (hb : d210420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148059, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148059, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148060 q = 1) (hb : d210980 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148060, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148060, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60547 (p : Pattern) (ha : d148148 p = 1) (hb : d210553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148106 q = 1) (hb : d210538 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60402 q ha hb
    | true =>
      simp only [d148106, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60404 q ha hb
  have h2 (q : Pattern) (ha : d148107 q = 1) (hb : d210539 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148108 q = 1) (hb : d210540 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148115 q = 1) (hb : d210543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60404 q ha hb
    | true =>
      simp only [d148115, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60405 q ha hb
  have h5 (q : Pattern) (ha : d148116 q = 1) (hb : d210544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148117 q = 1) (hb : d210545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148118 q = 1) (hb : d210546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148118, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148134 q = 1) (hb : d210543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148134, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60404 q ha hb
    | true =>
      simp only [d148134, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60409 q ha hb
  have h9 (q : Pattern) (ha : d148135 q = 1) (hb : d210544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148135, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148135, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148136 q = 1) (hb : d210545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148136, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148136, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148137 q = 1) (hb : d210551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148137, d210551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148137, d210551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148147 q = 1) (hb : d210552 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148147, d210552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148147, d210552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148148 q = 1) (hb : d210553 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148148, d210553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148148, d210553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro60548 (p : Pattern) (ha : d148154 p = 1) (hb : d210567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148149 q = 1) (hb : d210554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148149, d210554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60547 q ha hb
    | true =>
      simp only [d148149, d210554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148150 q = 1) (hb : d210555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148150, d210555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148150, d210555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148140 q = 1) (hb : d210562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d210562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60410 q ha hb
    | true =>
      simp only [d148140, d210562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148141 q = 1) (hb : d210563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d210563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d210563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148151 q = 1) (hb : d210564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148151, d210564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148151, d210564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148152 q = 1) (hb : d210565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148152, d210565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148152, d210565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148153 q = 1) (hb : d210566 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148153, d210566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148153, d210566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148154 q = 1) (hb : d210567 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148154, d210567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148154, d210567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro60549 (p : Pattern) (ha : d148179 p = 1) (hb : d210991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148159 q = 1) (hb : d210986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148159, d210986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60548 q ha hb
    | true =>
      simp only [d148159, d210986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60416 q ha hb
  have h3 (q : Pattern) (ha : d148160 q = 1) (hb : d210987 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148160, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148160, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148175 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148176 q = 1) (hb : d210988 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148176, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148176, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148177 q = 1) (hb : d210989 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148177, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148177, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148178 q = 1) (hb : d210990 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148178, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148178, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148179 q = 1) (hb : d210991 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148179, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148179, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60550 (p : Pattern) (ha : d148192 p = 1) (hb : d210997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148036 q = 1) (hb : d210422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148036, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60544 q ha hb
    | true =>
      simp only [d148036, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60545 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148055 q = 1) (hb : d210423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148055, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148055, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148056 q = 1) (hb : d210978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148056, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148056, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148057 q = 1) (hb : d210979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148057, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148057, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148061 q = 1) (hb : d210981 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148061, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148061, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60546 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148063 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148064 q = 1) (hb : d210982 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148064, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148064, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148065 q = 1) (hb : d210983 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148065, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148065, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148066 q = 1) (hb : d210984 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148066, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148066, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148067 q = 1) (hb : d210985 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148067, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148067, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148180 q = 1) (hb : d210992 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148180, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148180, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60549 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148187 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148188 q = 1) (hb : d210993 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148188, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148188, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148189 q = 1) (hb : d210994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148189, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148189, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148190 q = 1) (hb : d210995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148190, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148190, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148191 q = 1) (hb : d210996 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148191, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148191, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148192 q = 1) (hb : d210997 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148192, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148192, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60551 (p : Pattern) (ha : d148198 p = 1) (hb : d211003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148193 q = 1) (hb : d210998 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148193, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148193, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60550 q ha hb
  have h2 (q : Pattern) (ha : d148194 q = 1) (hb : d210999 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148194, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148194, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148195 q = 1) (hb : d211000 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148195, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148195, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148196 q = 1) (hb : d211001 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148196, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148196, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148197 q = 1) (hb : d211002 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148197, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148197, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148198 q = 1) (hb : d211003 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148198, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148198, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60552 (p : Pattern) (ha : d148332 p = 1) (hb : d210643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d148249 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60429 q ha hb
    | true =>
      simp only [d148249, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60430 q ha hb
  have h5 (q : Pattern) (ha : d148313 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d148313, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148329 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148329, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148330 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148330, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148331 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148331, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148332 q = 1) (hb : d210643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148332, d210643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148332, d210643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60553 (p : Pattern) (ha : d148354 p = 1) (hb : d210653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148249 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60429 q ha hb
    | true =>
      simp only [d148249, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60430 q ha hb
  have h4 (q : Pattern) (ha : d148313 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148313, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148329 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148329, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148330 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148330, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148331 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148331, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148338 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148343 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d148259 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60432 q ha hb
    | true =>
      simp only [d148259, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60433 q ha hb
  have h13 (q : Pattern) (ha : d148347 q = 1) (hb : d210649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148347, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148351 q = 1) (hb : d210650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148351, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148352 q = 1) (hb : d210651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148352, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148352, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148353 q = 1) (hb : d210652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148353, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148353, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148354 q = 1) (hb : d210653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148354, d210653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148354, d210653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60554 (p : Pattern) (ha : d148379 p = 1) (hb : d211010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148259 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60432 q ha hb
    | true =>
      simp only [d148259, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60433 q ha hb
  have h3 (q : Pattern) (ha : d148347 q = 1) (hb : d210649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148347, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148351 q = 1) (hb : d210650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148351, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148377 q = 1) (hb : d210651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148377, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148377, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148378 q = 1) (hb : d210652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148378, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148378, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148379 q = 1) (hb : d211010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148379, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148379, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60555 (p : Pattern) (ha : d148448 p = 1) (hb : d210762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d201628 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d201628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60462 q ha hb
    | true =>
      simp only [d148406, d201628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60460 q hb ha
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d201629 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d201629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d201629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d201630 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d201630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d201630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d210752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60460 q hb ha
    | true =>
      simp only [d148415, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60463 q ha hb
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d210753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d210754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d210755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148434 q = 1) (hb : d210752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60460 q hb ha
    | true =>
      simp only [d148434, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60467 q ha hb
  have h9 (q : Pattern) (ha : d148435 q = 1) (hb : d210753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148436 q = 1) (hb : d210754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148437 q = 1) (hb : d210760 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d210760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148437, d210760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148447 q = 1) (hb : d210761 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148447, d210761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148447, d210761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148448 q = 1) (hb : d210762 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148448, d210762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148448, d210762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro60556 (p : Pattern) (ha : d148454 p = 1) (hb : d210776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148449 q = 1) (hb : d210763 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148449, d210763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60555 q ha hb
    | true =>
      simp only [d148449, d210763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148450 q = 1) (hb : d210764 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148450, d210764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148450, d210764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d210771 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d210771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60468 q ha hb
    | true =>
      simp only [d148440, d210771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d210772 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d210772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d210772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148451 q = 1) (hb : d210773 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148451, d210773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148451, d210773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148452 q = 1) (hb : d210774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148452, d210774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148452, d210774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148453 q = 1) (hb : d210775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148453, d210775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148453, d210775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148454 q = 1) (hb : d210776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148454, d210776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148454, d210776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro60557 (p : Pattern) (ha : d148479 p = 1) (hb : d211021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148446 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148459 q = 1) (hb : d211016 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148459, d211016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60556 q ha hb
    | true =>
      simp only [d148459, d211016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60474 q ha hb
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d211017 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148460, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148476 q = 1) (hb : d211018 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148477 q = 1) (hb : d211019 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148478 q = 1) (hb : d211020 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148479 q = 1) (hb : d211021 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60558 (p : Pattern) (ha : d148492 p = 1) (hb : d211027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148267 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148355 q = 1) (hb : d210654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60552 q ha hb
    | true =>
      simp only [d148355, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60553 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148373 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148374 q = 1) (hb : d210655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148374, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148375 q = 1) (hb : d211008 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148375, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148376 q = 1) (hb : d211009 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148376, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148380 q = 1) (hb : d211011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148380, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60554 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148382 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148383 q = 1) (hb : d211012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148383, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148384 q = 1) (hb : d211013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148384, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148385 q = 1) (hb : d211014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148385, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148386 q = 1) (hb : d211015 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148386, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148480 q = 1) (hb : d211022 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148480, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60557 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148487 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148488 q = 1) (hb : d211023 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148488, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148489 q = 1) (hb : d211024 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148489, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148490 q = 1) (hb : d211025 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148490, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148491 q = 1) (hb : d211026 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148491, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148492 q = 1) (hb : d211027 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148492, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60559 (p : Pattern) (ha : d148498 p = 1) (hb : d211033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d211028 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60558 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d211029 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d211030 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d211031 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d211032 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d211033 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60560 (p : Pattern) (ha : d148504 p = 1) (hb : d211039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d147261 q = 1) (hb : d210920 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147261, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60523 q ha hb
    | true =>
      simp only [d147261, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60529 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147500 q = 1) (hb : d210947 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147500, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147500, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60535 q ha hb
  have h3 (q : Pattern) (ha : d147501 q = 1) (hb : d210948 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147501, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147501, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147858 q = 1) (hb : d210975 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147858, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147858, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60543 q ha hb
  have h5 (q : Pattern) (ha : d147859 q = 1) (hb : d210976 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147859, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147859, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147860 q = 1) (hb : d210977 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d147860, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147860, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148199 q = 1) (hb : d211004 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148199, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148199, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60551 q ha hb
  have h8 (q : Pattern) (ha : d148200 q = 1) (hb : d211005 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148200, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148200, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148201 q = 1) (hb : d211006 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148201, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148201, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148202 q = 1) (hb : d211007 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148202, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148202, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148499 q = 1) (hb : d211034 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148499, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148499, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60559 q ha hb
  have h12 (q : Pattern) (ha : d148500 q = 1) (hb : d211035 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148500, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148500, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148501 q = 1) (hb : d211036 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148501, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148501, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148502 q = 1) (hb : d211037 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148502, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148502, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148503 q = 1) (hb : d211038 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d148503, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148503, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148504 q = 1) (hb : d211039 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d148504, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148504, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro60561 (p : Pattern) (ha : d148510 p = 1) (hb : d211045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148505 q = 1) (hb : d211040 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d148505, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60560 q ha hb
    | true =>
      simp only [d148505, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148506 q = 1) (hb : d211041 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d148506, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148506, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148507 q = 1) (hb : d211042 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d148507, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148507, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148508 q = 1) (hb : d211043 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d148508, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148508, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148509 q = 1) (hb : d211044 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d148509, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148509, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148510 q = 1) (hb : d211045 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d148510, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148510, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60562 (p : Pattern) (ha : d148516 p = 1) (hb : d211051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148511 q = 1) (hb : d211046 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d148511, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60561 q ha hb
    | true =>
      simp only [d148511, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148512 q = 1) (hb : d211047 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d148512, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148512, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148513 q = 1) (hb : d211048 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d148513, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148513, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148514 q = 1) (hb : d211049 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d148514, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148514, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148515 q = 1) (hb : d211050 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d148515, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148515, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148516 q = 1) (hb : d211051 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d148516, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148516, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60563 (p : Pattern) (ha : d148522 p = 1) (hb : d211057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148517 q = 1) (hb : d211052 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d148517, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60562 q ha hb
    | true =>
      simp only [d148517, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148518 q = 1) (hb : d211053 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d148518, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148518, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148519 q = 1) (hb : d211054 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d148519, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148519, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148520 q = 1) (hb : d211055 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d148520, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148520, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148521 q = 1) (hb : d211056 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d148521, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148521, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148522 q = 1) (hb : d211057 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d148522, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148522, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60564 (p : Pattern) (ha : d148528 p = 1) (hb : d211063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148523 q = 1) (hb : d211058 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d148523, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60563 q ha hb
    | true =>
      simp only [d148523, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148524 q = 1) (hb : d211059 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d148524, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148524, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148525 q = 1) (hb : d211060 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d148525, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148525, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148526 q = 1) (hb : d211061 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d148526, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148526, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148527 q = 1) (hb : d211062 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d148527, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148527, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148528 q = 1) (hb : d211063 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d148528, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148528, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60565 (p : Pattern) (ha : d148534 p = 1) (hb : d211069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148529 q = 1) (hb : d211064 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d148529, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60564 q ha hb
    | true =>
      simp only [d148529, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148530 q = 1) (hb : d211065 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d148530, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148530, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148531 q = 1) (hb : d211066 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d148531, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148531, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148532 q = 1) (hb : d211067 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d148532, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148532, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148533 q = 1) (hb : d211068 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d148533, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148533, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148534 q = 1) (hb : d211069 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d148534, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148534, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60566 (p : Pattern) (ha : d148540 p = 1) (hb : d211075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148535 q = 1) (hb : d211070 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d148535, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60565 q ha hb
    | true =>
      simp only [d148535, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148536 q = 1) (hb : d211071 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d148536, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148536, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148537 q = 1) (hb : d211072 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d148537, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148537, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148538 q = 1) (hb : d211073 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d148538, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148538, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148539 q = 1) (hb : d211074 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d148539, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148539, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148540 q = 1) (hb : d211075 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d148540, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148540, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60567 (p : Pattern) (ha : d148546 p = 1) (hb : d211081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148541 q = 1) (hb : d211076 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d148541, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60566 q ha hb
    | true =>
      simp only [d148541, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148542 q = 1) (hb : d211077 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d148542, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148542, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148543 q = 1) (hb : d211078 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d148543, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148543, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148544 q = 1) (hb : d211079 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d148544, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148544, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148545 q = 1) (hb : d211080 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d148545, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148545, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148546 q = 1) (hb : d211081 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d148546, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148546, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro60568 (p : Pattern) (ha : d150039 p = 1) (hb : d209612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20982 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21009 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209554 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150035 q = 1) (hb : d209608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150035, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21031 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150036 q = 1) (hb : d209609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150036, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150037 q = 1) (hb : d209610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150037, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150038 q = 1) (hb : d209611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150038, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150039 q = 1) (hb : d209612 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150039, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60569 (p : Pattern) (ha : d150044 p = 1) (hb : d209619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20982 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20988 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21009 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209554 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150035 q = 1) (hb : d209608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150035, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21031 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150036 q = 1) (hb : d209609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150036, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150037 q = 1) (hb : d209610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150037, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150038 q = 1) (hb : d209611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150038, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21040 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21044 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21046 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d209561 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150040 q = 1) (hb : d209615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150040, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21052 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150041 q = 1) (hb : d209616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150041, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150042 q = 1) (hb : d209617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150042, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150043 q = 1) (hb : d209618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150043, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150044 q = 1) (hb : d209619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150044, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60570 (p : Pattern) (ha : d150051 p = 1) (hb : d210871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21046 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150040 q = 1) (hb : d209615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150040, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150041 q = 1) (hb : d209616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150041, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150049 q = 1) (hb : d209617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150049, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150050 q = 1) (hb : d209618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150050, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150051 q = 1) (hb : d210871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d210871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150051, d210871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60571 (p : Pattern) (ha : d150061 p = 1) (hb : d210881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150057 q = 1) (hb : d210877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d210877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150057, d210877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21112 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150058 q = 1) (hb : d210878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d210878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150058, d210878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150059 q = 1) (hb : d210879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d210879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150059, d210879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150060 q = 1) (hb : d210880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d210880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150060, d210880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150061 q = 1) (hb : d210881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d210881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150061, d210881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60572 (p : Pattern) (ha : d150067 p = 1) (hb : d210887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20976 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150045 q = 1) (hb : d209620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60568 q ha hb
    | true =>
      simp only [d150045, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60569 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21059 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150046 q = 1) (hb : d209621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150046, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150047 q = 1) (hb : d210869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d210869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150047, d210869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150048 q = 1) (hb : d210870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d210870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150048, d210870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150052 q = 1) (hb : d210872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d210872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150052, d210872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60570 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150053 q = 1) (hb : d210873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d210873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150053, d210873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150054 q = 1) (hb : d210874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d210874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150054, d210874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150055 q = 1) (hb : d210875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d210875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150055, d210875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150056 q = 1) (hb : d210876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d210876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150056, d210876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150062 q = 1) (hb : d210882 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d210882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150062, d210882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60571 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150063 q = 1) (hb : d210883 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d210883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150063, d210883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150064 q = 1) (hb : d210884 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d210884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150064, d210884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150065 q = 1) (hb : d210885 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d210885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150065, d210885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150066 q = 1) (hb : d210886 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d210886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150066, d210886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150067 q = 1) (hb : d210887 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d210887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150067, d210887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60573 (p : Pattern) (ha : d150073 p = 1) (hb : d210893 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d150068 q = 1) (hb : d210888 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d210888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150068, d210888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60572 q ha hb
  have h8 (q : Pattern) (ha : d150069 q = 1) (hb : d210889 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d210889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150069, d210889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150070 q = 1) (hb : d210890 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d210890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150070, d210890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150071 q = 1) (hb : d210891 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d210891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150071, d210891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150072 q = 1) (hb : d210892 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d210892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150072, d210892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150073 q = 1) (hb : d210893 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d210893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d150073, d210893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro60574 (p : Pattern) (ha : d150078 p = 1) (hb : d209752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21211 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150074 q = 1) (hb : d209748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150074, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21253 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150075 q = 1) (hb : d209749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150075, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150076 q = 1) (hb : d209750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150076, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150077 q = 1) (hb : d209751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150077, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150078 q = 1) (hb : d209752 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d209752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150078, d209752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60575 (p : Pattern) (ha : d150083 p = 1) (hb : d209762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21172 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21211 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150074 q = 1) (hb : d209748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150074, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21253 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150075 q = 1) (hb : d209749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150075, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150076 q = 1) (hb : d209750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150076, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150077 q = 1) (hb : d209751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150077, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21263 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21268 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21270 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d209757 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150079 q = 1) (hb : d209758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150079, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21277 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150080 q = 1) (hb : d209759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150080, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150081 q = 1) (hb : d209760 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150081, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150082 q = 1) (hb : d209761 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150082, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150083 q = 1) (hb : d209762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d209762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150083, d209762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60576 (p : Pattern) (ha : d150090 p = 1) (hb : d210896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21270 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150079 q = 1) (hb : d209758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150079, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21277 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150080 q = 1) (hb : d209759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150080, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150088 q = 1) (hb : d209760 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150088, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150089 q = 1) (hb : d209761 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150089, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150090 q = 1) (hb : d210896 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d210896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150090, d210896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60577 (p : Pattern) (ha : d150100 p = 1) (hb : d210907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150096 q = 1) (hb : d210903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d210903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150096, d210903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21389 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150097 q = 1) (hb : d210904 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d210904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150097, d210904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150098 q = 1) (hb : d210905 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d210905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150098, d210905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150099 q = 1) (hb : d210906 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d210906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150099, d210906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150100 q = 1) (hb : d210907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d210907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150100, d210907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60578 (p : Pattern) (ha : d150106 p = 1) (hb : d210913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21164 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150084 q = 1) (hb : d209763 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60574 q ha hb
    | true =>
      simp only [d150084, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60575 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21295 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150085 q = 1) (hb : d209764 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150085, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150086 q = 1) (hb : d210894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d210894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150086, d210894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150087 q = 1) (hb : d210895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d210895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150087, d210895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150091 q = 1) (hb : d210897 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d210897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150091, d210897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60576 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21304 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150092 q = 1) (hb : d210898 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d210898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150092, d210898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150093 q = 1) (hb : d210899 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d210899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150093, d210899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150094 q = 1) (hb : d210900 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d210900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150094, d210900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150095 q = 1) (hb : d210901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d210901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150095, d210901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150101 q = 1) (hb : d210908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d210908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150101, d210908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60577 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21405 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150102 q = 1) (hb : d210909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d210909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150102, d210909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150103 q = 1) (hb : d210910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d210910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150103, d210910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150104 q = 1) (hb : d210911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d210911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150104, d210911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150105 q = 1) (hb : d210912 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d210912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150105, d210912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150106 q = 1) (hb : d210913 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d210913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150106, d210913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60579 (p : Pattern) (ha : d150112 p = 1) (hb : d210919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150107 q = 1) (hb : d210914 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d210914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150107, d210914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60578 q ha hb
  have h2 (q : Pattern) (ha : d150108 q = 1) (hb : d210915 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d210915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150108, d210915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150109 q = 1) (hb : d210916 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d210916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150109, d210916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150110 q = 1) (hb : d210917 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d210917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150110, d210917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150111 q = 1) (hb : d210918 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d210918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150111, d210918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150112 q = 1) (hb : d210919 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d210919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150112, d210919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60580 (p : Pattern) (ha : d150118 p = 1) (hb : d209950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209945 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150114 q = 1) (hb : d209946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150114, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150115 q = 1) (hb : d209947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150115, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150116 q = 1) (hb : d209948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150116, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150117 q = 1) (hb : d209949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150117, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150118 q = 1) (hb : d209950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d209950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150118, d209950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60581 (p : Pattern) (ha : d150123 p = 1) (hb : d209960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150114 q = 1) (hb : d209946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150114, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150115 q = 1) (hb : d209947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150115, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150116 q = 1) (hb : d209948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150116, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150117 q = 1) (hb : d209949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150117, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21566 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21571 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d209955 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150119 q = 1) (hb : d209956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150119, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150120 q = 1) (hb : d209957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150120, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150121 q = 1) (hb : d209958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150121, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150122 q = 1) (hb : d209959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150122, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150123 q = 1) (hb : d209960 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d209960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150123, d209960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60582 (p : Pattern) (ha : d150130 p = 1) (hb : d210923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150119 q = 1) (hb : d209956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150119, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150120 q = 1) (hb : d209957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150120, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150128 q = 1) (hb : d209958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150128, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150129 q = 1) (hb : d209959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150129, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150130 q = 1) (hb : d210923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d210923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150130, d210923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60583 (p : Pattern) (ha : d150140 p = 1) (hb : d210934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210929 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150136 q = 1) (hb : d210930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d210930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150136, d210930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21706 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150137 q = 1) (hb : d210931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d210931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150137, d210931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150138 q = 1) (hb : d210932 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d210932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150138, d210932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150139 q = 1) (hb : d210933 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d210933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150139, d210933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150140 q = 1) (hb : d210934 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d210934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150140, d210934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60584 (p : Pattern) (ha : d150146 p = 1) (hb : d210940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21463 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150124 q = 1) (hb : d209961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60580 q ha hb
    | true =>
      simp only [d150124, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60581 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150125 q = 1) (hb : d209962 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150125, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150126 q = 1) (hb : d210921 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d210921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150126, d210921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150127 q = 1) (hb : d210922 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d210922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150127, d210922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150131 q = 1) (hb : d210924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d210924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150131, d210924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60582 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21607 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150132 q = 1) (hb : d210925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d210925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150132, d210925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150133 q = 1) (hb : d210926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d210926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150133, d210926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150134 q = 1) (hb : d210927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d210927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150134, d210927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150135 q = 1) (hb : d210928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d210928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150135, d210928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150141 q = 1) (hb : d210935 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d210935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150141, d210935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60583 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21722 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150142 q = 1) (hb : d210936 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d210936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150142, d210936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150143 q = 1) (hb : d210937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d210937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150143, d210937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150144 q = 1) (hb : d210938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d210938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150144, d210938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150145 q = 1) (hb : d210939 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d210939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150145, d210939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150146 q = 1) (hb : d210940 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d210940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150146, d210940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60585 (p : Pattern) (ha : d150152 p = 1) (hb : d210946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150147 q = 1) (hb : d210941 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d210941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150147, d210941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60584 q ha hb
  have h2 (q : Pattern) (ha : d150148 q = 1) (hb : d210942 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d210942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150148, d210942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150149 q = 1) (hb : d210943 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d210943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150149, d210943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150150 q = 1) (hb : d210944 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d210944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150150, d210944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150151 q = 1) (hb : d210945 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d210945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150151, d210945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150152 q = 1) (hb : d210946 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d210946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150152, d210946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60586 (p : Pattern) (ha : d150159 p = 1) (hb : d210168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d210163 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150155 q = 1) (hb : d210164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150155, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150156 q = 1) (hb : d210165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150156, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150157 q = 1) (hb : d210166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150157, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150158 q = 1) (hb : d210167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150158, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150159 q = 1) (hb : d210168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150159, d210168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150159, d210168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60587 (p : Pattern) (ha : d150164 p = 1) (hb : d210178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d210163 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150155 q = 1) (hb : d210164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150155, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150156 q = 1) (hb : d210165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150156, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150157 q = 1) (hb : d210166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150157, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150158 q = 1) (hb : d210167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150158, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21972 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21977 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d210173 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150160 q = 1) (hb : d210174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150160, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150161 q = 1) (hb : d210175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150161, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150162 q = 1) (hb : d210176 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150162, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150162, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150163 q = 1) (hb : d210177 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150163, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150163, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150164 q = 1) (hb : d210178 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150164, d210178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150164, d210178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60588 (p : Pattern) (ha : d150171 p = 1) (hb : d210951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150160 q = 1) (hb : d210174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150160, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150161 q = 1) (hb : d210175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150161, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150169 q = 1) (hb : d210176 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150169, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150169, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150170 q = 1) (hb : d210177 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150170, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150170, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150171 q = 1) (hb : d210951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d210951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150171, d210951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60589 (p : Pattern) (ha : d150181 p = 1) (hb : d210962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150177 q = 1) (hb : d210958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d210958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150177, d210958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22188 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150178 q = 1) (hb : d210959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d210959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150178, d210959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150179 q = 1) (hb : d210960 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d210960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150179, d210960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150180 q = 1) (hb : d210961 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d210961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150180, d210961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150181 q = 1) (hb : d210962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d210962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150181, d210962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60590 (p : Pattern) (ha : d150187 p = 1) (hb : d210968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21816 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150165 q = 1) (hb : d210179 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150165, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60586 q ha hb
    | true =>
      simp only [d150165, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60587 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22010 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150166 q = 1) (hb : d210180 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150166, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150166, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150167 q = 1) (hb : d210949 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150167, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150168 q = 1) (hb : d210950 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150168, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150172 q = 1) (hb : d210952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150172, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60588 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22019 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150173 q = 1) (hb : d210953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150173, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150174 q = 1) (hb : d210954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150174, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150175 q = 1) (hb : d210955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150175, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150176 q = 1) (hb : d210956 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150176, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150182 q = 1) (hb : d210963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150182, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60589 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150183 q = 1) (hb : d210964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150183, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150184 q = 1) (hb : d210965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150184, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150185 q = 1) (hb : d210966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150185, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150186 q = 1) (hb : d210967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150186, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150187 q = 1) (hb : d210968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150187, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60591 (p : Pattern) (ha : d150193 p = 1) (hb : d210974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150188 q = 1) (hb : d210969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150188, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60590 q ha hb
  have h2 (q : Pattern) (ha : d150189 q = 1) (hb : d210970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150189, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150190 q = 1) (hb : d210971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150190, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150191 q = 1) (hb : d210972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150191, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150192 q = 1) (hb : d210973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150192, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150193 q = 1) (hb : d210974 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150193, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60592 (p : Pattern) (ha : d150201 p = 1) (hb : d210411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150197 q = 1) (hb : d210407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150197, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150198 q = 1) (hb : d210408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150198, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150199 q = 1) (hb : d210409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150199, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150200 q = 1) (hb : d210410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150200, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150201 q = 1) (hb : d210411 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150201, d210411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150201, d210411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60593 (p : Pattern) (ha : d150206 p = 1) (hb : d210421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150197 q = 1) (hb : d210407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150197, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150198 q = 1) (hb : d210408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150198, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150199 q = 1) (hb : d210409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150199, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150200 q = 1) (hb : d210410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150200, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22445 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22450 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d210416 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150202 q = 1) (hb : d210417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150202, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150203 q = 1) (hb : d210418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150203, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150204 q = 1) (hb : d210419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150204, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150204, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150205 q = 1) (hb : d210420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150205, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150205, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150206 q = 1) (hb : d210421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150206, d210421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150206, d210421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60594 (p : Pattern) (ha : d150213 p = 1) (hb : d210980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150202 q = 1) (hb : d210417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150202, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150203 q = 1) (hb : d210418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150203, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150211 q = 1) (hb : d210419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150211, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150211, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150212 q = 1) (hb : d210420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150212, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150212, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150213 q = 1) (hb : d210980 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150213, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60595 (p : Pattern) (ha : d150223 p = 1) (hb : d210991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210986 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150219 q = 1) (hb : d210987 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150219, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22653 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150220 q = 1) (hb : d210988 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150220, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150221 q = 1) (hb : d210989 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150221, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150222 q = 1) (hb : d210990 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150222, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150223 q = 1) (hb : d210991 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150223, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60596 (p : Pattern) (ha : d150229 p = 1) (hb : d210997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150207 q = 1) (hb : d210422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150207, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60592 q ha hb
    | true =>
      simp only [d150207, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60593 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150208 q = 1) (hb : d210423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150208, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150208, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150209 q = 1) (hb : d210978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150209, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150210 q = 1) (hb : d210979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150210, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150214 q = 1) (hb : d210981 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150214, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60594 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22492 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150215 q = 1) (hb : d210982 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150215, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150216 q = 1) (hb : d210983 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150216, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150217 q = 1) (hb : d210984 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150217, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150218 q = 1) (hb : d210985 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150218, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150224 q = 1) (hb : d210992 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150224, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60595 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22669 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150225 q = 1) (hb : d210993 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150225, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150226 q = 1) (hb : d210994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150226, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150227 q = 1) (hb : d210995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150227, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150228 q = 1) (hb : d210996 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150228, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150229 q = 1) (hb : d210997 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150229, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60597 (p : Pattern) (ha : d150235 p = 1) (hb : d211003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150230 q = 1) (hb : d210998 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150230, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60596 q ha hb
  have h2 (q : Pattern) (ha : d150231 q = 1) (hb : d210999 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150231, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150232 q = 1) (hb : d211000 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150232, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150233 q = 1) (hb : d211001 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150233, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150234 q = 1) (hb : d211002 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150234, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150235 q = 1) (hb : d211003 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150235, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60598 (p : Pattern) (ha : d150244 p = 1) (hb : d210643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150240 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150240, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150241 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150241, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150242 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150242, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150243 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150243, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150244 q = 1) (hb : d210643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150244, d210643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150244, d210643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60599 (p : Pattern) (ha : d150249 p = 1) (hb : d210653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150240 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150240, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150241 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150241, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150242 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150242, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150243 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150243, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22878 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22883 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150245 q = 1) (hb : d210649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150245, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150246 q = 1) (hb : d210650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150246, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150247 q = 1) (hb : d210651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150247, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150247, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150248 q = 1) (hb : d210652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150248, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150248, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150249 q = 1) (hb : d210653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150249, d210653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150249, d210653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60600 (p : Pattern) (ha : d150256 p = 1) (hb : d211010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150245 q = 1) (hb : d210649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150245, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150246 q = 1) (hb : d210650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150246, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150254 q = 1) (hb : d210651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150254, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150254, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150255 q = 1) (hb : d210652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150255, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150255, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150256 q = 1) (hb : d211010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150256, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150256, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60601 (p : Pattern) (ha : d150266 p = 1) (hb : d211021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211016 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150262 q = 1) (hb : d211017 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150262, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150262, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23059 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150263 q = 1) (hb : d211018 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150263, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150263, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150264 q = 1) (hb : d211019 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150264, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150264, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150265 q = 1) (hb : d211020 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150265, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150265, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150266 q = 1) (hb : d211021 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150266, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150266, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60602 (p : Pattern) (ha : d150272 p = 1) (hb : d211027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150250 q = 1) (hb : d210654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150250, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60598 q ha hb
    | true =>
      simp only [d150250, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60599 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150251 q = 1) (hb : d210655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150251, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150251, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150252 q = 1) (hb : d211008 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150252, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150252, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150253 q = 1) (hb : d211009 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150253, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150253, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150257 q = 1) (hb : d211011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150257, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150257, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60600 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22925 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150258 q = 1) (hb : d211012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150258, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150258, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150259 q = 1) (hb : d211013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150259, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150259, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150260 q = 1) (hb : d211014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150260, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150260, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150261 q = 1) (hb : d211015 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150261, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150261, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150267 q = 1) (hb : d211022 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150267, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150267, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60601 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23075 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150268 q = 1) (hb : d211023 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150268, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150268, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150269 q = 1) (hb : d211024 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150269, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150269, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150270 q = 1) (hb : d211025 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150270, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150270, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150271 q = 1) (hb : d211026 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150271, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150271, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150272 q = 1) (hb : d211027 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150272, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150272, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60603 (p : Pattern) (ha : d150278 p = 1) (hb : d211033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150273 q = 1) (hb : d211028 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150273, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150273, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60602 q ha hb
  have h2 (q : Pattern) (ha : d150274 q = 1) (hb : d211029 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150274, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150274, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150275 q = 1) (hb : d211030 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150275, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150275, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150276 q = 1) (hb : d211031 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150276, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150276, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150277 q = 1) (hb : d211032 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150277, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150277, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150278 q = 1) (hb : d211033 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150278, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150278, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60604 (p : Pattern) (ha : d150284 p = 1) (hb : d211039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d150113 q = 1) (hb : d210920 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150113, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60573 q ha hb
    | true =>
      simp only [d150113, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60579 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150153 q = 1) (hb : d210947 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150153, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150153, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60585 q ha hb
  have h3 (q : Pattern) (ha : d150154 q = 1) (hb : d210948 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150154, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150154, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150194 q = 1) (hb : d210975 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150194, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150194, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60591 q ha hb
  have h5 (q : Pattern) (ha : d150195 q = 1) (hb : d210976 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150195, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150195, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150196 q = 1) (hb : d210977 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150196, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150196, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150236 q = 1) (hb : d211004 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150236, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150236, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60597 q ha hb
  have h8 (q : Pattern) (ha : d150237 q = 1) (hb : d211005 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150237, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150237, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150238 q = 1) (hb : d211006 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150238, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150238, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150239 q = 1) (hb : d211007 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150239, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150239, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150279 q = 1) (hb : d211034 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150279, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150279, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60603 q ha hb
  have h12 (q : Pattern) (ha : d150280 q = 1) (hb : d211035 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150280, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150280, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150281 q = 1) (hb : d211036 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150281, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150281, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150282 q = 1) (hb : d211037 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150282, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150282, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150283 q = 1) (hb : d211038 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150283, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150283, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150284 q = 1) (hb : d211039 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150284, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150284, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro60605 (p : Pattern) (ha : d150290 p = 1) (hb : d211045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150285 q = 1) (hb : d211040 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150285, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60604 q ha hb
    | true =>
      simp only [d150285, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150286 q = 1) (hb : d211041 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150286, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150286, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150287 q = 1) (hb : d211042 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150287, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150287, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150288 q = 1) (hb : d211043 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150288, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150288, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150289 q = 1) (hb : d211044 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150289, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150289, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150290 q = 1) (hb : d211045 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150290, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150290, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60606 (p : Pattern) (ha : d150296 p = 1) (hb : d211051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150291 q = 1) (hb : d211046 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150291, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60605 q ha hb
    | true =>
      simp only [d150291, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150292 q = 1) (hb : d211047 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150292, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150292, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150293 q = 1) (hb : d211048 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150293, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150293, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150294 q = 1) (hb : d211049 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150294, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150294, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150295 q = 1) (hb : d211050 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150295, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150295, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150296 q = 1) (hb : d211051 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150296, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150296, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60607 (p : Pattern) (ha : d150302 p = 1) (hb : d211057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150297 q = 1) (hb : d211052 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150297, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60606 q ha hb
    | true =>
      simp only [d150297, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150298 q = 1) (hb : d211053 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150298, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150298, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150299 q = 1) (hb : d211054 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150299, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150299, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150300 q = 1) (hb : d211055 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150300, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150300, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150301 q = 1) (hb : d211056 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150301, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150301, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150302 q = 1) (hb : d211057 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150302, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150302, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60608 (p : Pattern) (ha : d150308 p = 1) (hb : d211063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150303 q = 1) (hb : d211058 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150303, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60607 q ha hb
    | true =>
      simp only [d150303, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150304 q = 1) (hb : d211059 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150304, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150304, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150305 q = 1) (hb : d211060 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150305, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150305, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150306 q = 1) (hb : d211061 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150306, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150306, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150307 q = 1) (hb : d211062 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150307, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150307, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150308 q = 1) (hb : d211063 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150308, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150308, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60609 (p : Pattern) (ha : d150314 p = 1) (hb : d211069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150309 q = 1) (hb : d211064 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150309, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60608 q ha hb
    | true =>
      simp only [d150309, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150310 q = 1) (hb : d211065 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150310, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150310, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150311 q = 1) (hb : d211066 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150311, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150311, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150312 q = 1) (hb : d211067 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150312, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150312, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150313 q = 1) (hb : d211068 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150313, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150313, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150314 q = 1) (hb : d211069 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150314, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150314, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60610 (p : Pattern) (ha : d150320 p = 1) (hb : d211075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150315 q = 1) (hb : d211070 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150315, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60609 q ha hb
    | true =>
      simp only [d150315, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150316 q = 1) (hb : d211071 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150316, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150316, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150317 q = 1) (hb : d211072 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150317, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150317, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150318 q = 1) (hb : d211073 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150318, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150318, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150319 q = 1) (hb : d211074 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150319, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150319, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150320 q = 1) (hb : d211075 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150320, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150320, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60611 (p : Pattern) (ha : d150326 p = 1) (hb : d211081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150321 q = 1) (hb : d211076 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150321, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60610 q ha hb
    | true =>
      simp only [d150321, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150322 q = 1) (hb : d211077 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150322, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150322, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150323 q = 1) (hb : d211078 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150323, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150323, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150324 q = 1) (hb : d211079 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150324, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150324, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150325 q = 1) (hb : d211080 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150325, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150325, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150326 q = 1) (hb : d211081 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150326, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150326, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60612 (p : Pattern) (ha : d9381 p = 1) (hb : d241832 p = 1) : d30758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d241830 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d135 q = 1) (hb : d241831 q = 1) : d30635 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d241831, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d135, d241831, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5448 q = 1) (hb : d241832 q = 1) : d30756 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5448, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5449 q = 1) (hb : d241832 q = 1) : d30757 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5449, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23 q = 1) (hb : d241832 q = 1) : d23 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9381 q = 1) (hb : d241832 q = 1) : d30758 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d30758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9381, d30758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60613 (p : Pattern) (ha : d16081 p = 1) (hb : d241832 p = 1) : d30999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
    | true =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d241832 q = 1) : d30761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d241832 q = 1) : d30762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d241832 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d241832 q = 1) : d30763 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d30763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d30763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d241832 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d241832 q = 1) : d30999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d30999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16081, d30999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60614 (p : Pattern) (ha : d23140 p = 1) (hb : d241832 p = 1) : d243740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23135 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60613 q ha hb
    | true =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23136 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23137 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d241832 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23138 q = 1) (hb : d241832 q = 1) : d243738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23138, d243738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23138, d243738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d241832 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23139 q = 1) (hb : d241832 q = 1) : d243739 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23139, d243739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23139, d243739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23140 q = 1) (hb : d241832 q = 1) : d243740 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23140, d243740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23140, d243740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro60615 (p : Pattern) (ha : d23146 p = 1) (hb : d241832 p = 1) : d243746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d241832 q = 1) : d243744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23145 q = 1) (hb : d241832 q = 1) : d243745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23145, d243745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23145, d243745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23146 q = 1) (hb : d241832 q = 1) : d243746 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23146, d243746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23146, d243746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro60616 (p : Pattern) (ha : d211086 p = 1) (hb : d241832 p = 1) : d243752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d241832 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d241832 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23147 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60615 q ha hb
    | true =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211082 q = 1) (hb : d241832 q = 1) : d243748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211082, d243748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211082, d243748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d241832 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211083 q = 1) (hb : d241832 q = 1) : d243749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211083, d243749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211083, d243749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211084 q = 1) (hb : d241832 q = 1) : d243750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211084, d243750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211084, d243750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211085 q = 1) (hb : d241832 q = 1) : d243751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211085, d243751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211085, d243751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211086 q = 1) (hb : d241832 q = 1) : d243752 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211086, d243752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211086, d243752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60617 (p : Pattern) (ha : d23153 p = 1) (hb : d241832 p = 1) : d243753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d241832 q = 1) : d243744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23145 q = 1) (hb : d241832 q = 1) : d243745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23145, d243745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23145, d243745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23153 q = 1) (hb : d241832 q = 1) : d243753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23153, d243753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23153, d243753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro60618 (p : Pattern) (ha : d211091 p = 1) (hb : d241832 p = 1) : d243759 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d241832 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d241832 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23147 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60615 q ha hb
    | true =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211082 q = 1) (hb : d241832 q = 1) : d243748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211082, d243748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211082, d243748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d241832 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211083 q = 1) (hb : d241832 q = 1) : d243749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211083, d243749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211083, d243749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211084 q = 1) (hb : d241832 q = 1) : d243750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211084, d243750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211084, d243750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211085 q = 1) (hb : d241832 q = 1) : d243751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211085, d243751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211085, d243751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d241832 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d241832 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d241832 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23154 q = 1) (hb : d241832 q = 1) : d243754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60617 q ha hb
    | true =>
      simp only [d23154, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211087 q = 1) (hb : d241832 q = 1) : d243755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211087, d243755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211087, d243755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d241832 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d211088 q = 1) (hb : d241832 q = 1) : d243756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211088, d243756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211088, d243756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211089 q = 1) (hb : d241832 q = 1) : d243757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211089, d243757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211089, d243757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211090 q = 1) (hb : d241832 q = 1) : d243758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211090, d243758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211090, d243758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d211091 q = 1) (hb : d241832 q = 1) : d243759 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211091, d243759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211091, d243759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro60619 (p : Pattern) (ha : d211098 p = 1) (hb : d241832 p = 1) : d243766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d241832 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23154 q = 1) (hb : d241832 q = 1) : d243754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60617 q ha hb
    | true =>
      simp only [d23154, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211087 q = 1) (hb : d241832 q = 1) : d243755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211087, d243755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211087, d243755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d241832 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211088 q = 1) (hb : d241832 q = 1) : d243756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211088, d243756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211088, d243756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211096 q = 1) (hb : d241832 q = 1) : d243764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211096, d243764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211096, d243764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211097 q = 1) (hb : d241832 q = 1) : d243765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211097, d243765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211097, d243765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211098 q = 1) (hb : d241832 q = 1) : d243766 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211098, d243766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211098, d243766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60620 (p : Pattern) (ha : d16166 p = 1) (hb : d241832 p = 1) : d31136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d241832 q = 1) : d30852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
    | true =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d241832 q = 1) : d30853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d241832 q = 1) : d30854 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d241832 q = 1) : d30855 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d241832 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d241832 q = 1) : d30856 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d30856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d30856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d241832 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d241832 q = 1) : d31136 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d31136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16166, d31136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro60621 (p : Pattern) (ha : d23177 p = 1) (hb : d241832 p = 1) : d243777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23172 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60620 q ha hb
    | true =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23173 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23174 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d241832 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23175 q = 1) (hb : d241832 q = 1) : d243775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23175, d243775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23175, d243775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d241832 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23176 q = 1) (hb : d241832 q = 1) : d243776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23176, d243776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23176, d243776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23177 q = 1) (hb : d241832 q = 1) : d243777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23177, d243777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23177, d243777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro60622 (p : Pattern) (ha : d23183 p = 1) (hb : d241832 p = 1) : d243783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23178 q = 1) (hb : d241832 q = 1) : d243778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60621 q ha hb
    | true =>
      simp only [d23178, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23179 q = 1) (hb : d241832 q = 1) : d243779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d241832 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23180 q = 1) (hb : d241832 q = 1) : d243780 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23180, d243780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23180, d243780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23181 q = 1) (hb : d241832 q = 1) : d243781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23181, d243781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23181, d243781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23182 q = 1) (hb : d241832 q = 1) : d243782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23182, d243782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23182, d243782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23183 q = 1) (hb : d241832 q = 1) : d243783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23183, d243783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23183, d243783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro60623 (p : Pattern) (ha : d211108 p = 1) (hb : d241832 p = 1) : d243789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d241832 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23184 q = 1) (hb : d241832 q = 1) : d243784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23184, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60622 q ha hb
    | true =>
      simp only [d23184, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211104 q = 1) (hb : d241832 q = 1) : d243785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211104, d243785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211104, d243785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d241832 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211105 q = 1) (hb : d241832 q = 1) : d243786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211105, d243786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211105, d243786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211106 q = 1) (hb : d241832 q = 1) : d243787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211106, d243787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211106, d243787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211107 q = 1) (hb : d241832 q = 1) : d243788 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211107, d243788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211107, d243788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211108 q = 1) (hb : d241832 q = 1) : d243789 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211108, d243789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211108, d243789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60624 (p : Pattern) (ha : d211114 p = 1) (hb : d241832 p = 1) : d243795 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d241832 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211092 q = 1) (hb : d241832 q = 1) : d243760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211092, d243760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60616 q ha hb
    | true =>
      simp only [d211092, d243760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60618 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d241832 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211093 q = 1) (hb : d241832 q = 1) : d243761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211093, d243761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211093, d243761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211094 q = 1) (hb : d241832 q = 1) : d243762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211094, d243762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211094, d243762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211095 q = 1) (hb : d241832 q = 1) : d243763 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211095, d243763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211095, d243763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211099 q = 1) (hb : d241832 q = 1) : d243767 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211099, d243767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211099, d243767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60619 q ha hb
  have h8 (q : Pattern) (ha : d211100 q = 1) (hb : d241832 q = 1) : d243768 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211100, d243768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211100, d243768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d211101 q = 1) (hb : d241832 q = 1) : d243769 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211101, d243769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211101, d243769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d211102 q = 1) (hb : d241832 q = 1) : d243770 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211102, d243770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211102, d243770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211103 q = 1) (hb : d241832 q = 1) : d243771 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211103, d243771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211103, d243771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d211109 q = 1) (hb : d241832 q = 1) : d243790 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211109, d243790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211109, d243790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60623 q ha hb
  have h13 (q : Pattern) (ha : d211110 q = 1) (hb : d241832 q = 1) : d243791 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211110, d243791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211110, d243791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d211111 q = 1) (hb : d241832 q = 1) : d243792 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211111, d243792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211111, d243792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d211112 q = 1) (hb : d241832 q = 1) : d243793 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211112, d243793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211112, d243793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d211113 q = 1) (hb : d241832 q = 1) : d243794 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211113, d243794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211113, d243794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211114 q = 1) (hb : d241832 q = 1) : d243795 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211114, d243795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211114, d243795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro60625 (p : Pattern) (ha : d23205 p = 1) (hb : d241832 p = 1) : d243805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60615 q ha hb
    | true =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d241832 q = 1) : d243801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d241832 q = 1) : d243802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d241832 q = 1) : d243803 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d241832 q = 1) : d243804 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23205 q = 1) (hb : d241832 q = 1) : d243805 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro60626 (p : Pattern) (ha : d23212 p = 1) (hb : d241832 p = 1) : d243812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60615 q ha hb
    | true =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d241832 q = 1) : d243801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d241832 q = 1) : d243802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d241832 q = 1) : d243803 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d241832 q = 1) : d243804 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d241832 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23154 q = 1) (hb : d241832 q = 1) : d243754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60617 q ha hb
    | true =>
      simp only [d23154, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23208 q = 1) (hb : d241832 q = 1) : d243808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23208, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23209 q = 1) (hb : d241832 q = 1) : d243809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23209, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23210 q = 1) (hb : d241832 q = 1) : d243810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23211 q = 1) (hb : d241832 q = 1) : d243811 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23212 q = 1) (hb : d241832 q = 1) : d243812 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23212, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro60627 (p : Pattern) (ha : d23297 p = 1) (hb : d241832 p = 1) : d243873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60615 q ha hb
    | true =>
      simp only [d23147, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d241832 q = 1) : d243801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d241832 q = 1) : d243802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d241832 q = 1) : d243803 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d241832 q = 1) : d243804 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d241832 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23297 q = 1) (hb : d241832 q = 1) : d243873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23297, d243873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23297, d243873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60628 (p : Pattern) (ha : d23217 p = 1) (hb : d241832 p = 1) : d243817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d241832 q = 1) : d243744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23216 q = 1) (hb : d241832 q = 1) : d243816 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23216, d243816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23216, d243816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23217 q = 1) (hb : d241832 q = 1) : d243817 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23217, d243817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23217, d243817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro60629 (p : Pattern) (ha : d23224 p = 1) (hb : d241832 p = 1) : d243824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23222 q = 1) (hb : d241832 q = 1) : d243822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23222, d243822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23222, d243822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23223 q = 1) (hb : d241832 q = 1) : d243823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23223, d243823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23223, d243823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23224 q = 1) (hb : d241832 q = 1) : d243824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23224, d243824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23224, d243824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro60630 (p : Pattern) (ha : d23230 p = 1) (hb : d241832 p = 1) : d30989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315 q = 1) (hb : d241831 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d241831, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315, d241831, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23228 q = 1) (hb : d241832 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23228, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23229 q = 1) (hb : d241832 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23229, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20 q = 1) (hb : d241830 q = 1) : d20 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d135 q = 1) (hb : d241831 q = 1) : d30635 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d241831, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d135, d241831, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5448 q = 1) (hb : d241832 q = 1) : d30756 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5448, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d5449 q = 1) (hb : d241832 q = 1) : d30757 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5449, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h17 (q : Pattern) (ha : d23230 q = 1) (hb : d241832 q = 1) : d30989 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23230, d30989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23230, d30989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro60631 (p : Pattern) (ha : d23236 p = 1) (hb : d241832 p = 1) : d243828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9382 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
    | true =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9384 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12493 q = 1) (hb : d241832 q = 1) : d30761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12494 q = 1) (hb : d241832 q = 1) : d30762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12494, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23235 q = 1) (hb : d241832 q = 1) : d30994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d30994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23235, d30994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d241832 q = 1) : d28 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12495 q = 1) (hb : d241832 q = 1) : d30763 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d30763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12495, d30763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23236 q = 1) (hb : d241832 q = 1) : d243828 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23236, d243828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23236, d243828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro60632 (p : Pattern) (ha : d23242 p = 1) (hb : d241832 p = 1) : d243834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23237 q = 1) (hb : d241832 q = 1) : d243829 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60631 q ha hb
    | true =>
      simp only [d23237, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60613 q ha hb
  have h2 (q : Pattern) (ha : d23238 q = 1) (hb : d241832 q = 1) : d243830 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23239 q = 1) (hb : d241832 q = 1) : d243831 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23135 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60613 q ha hb
    | true =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23136 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23137 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23240 q = 1) (hb : d241832 q = 1) : d243832 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23240, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d241832 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23138 q = 1) (hb : d241832 q = 1) : d243738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23138, d243738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23138, d243738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23241 q = 1) (hb : d241832 q = 1) : d243833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23241, d243833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23241, d243833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23242 q = 1) (hb : d241832 q = 1) : d243834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23242, d243834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23242, d243834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro60633 (p : Pattern) (ha : d23248 p = 1) (hb : d241832 p = 1) : d243840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23243 q = 1) (hb : d241832 q = 1) : d243835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23243, d243835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60632 q ha hb
    | true =>
      simp only [d23243, d243835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23244 q = 1) (hb : d241832 q = 1) : d243836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23244, d243836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23244, d243836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23245 q = 1) (hb : d241832 q = 1) : d243837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23245, d243837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23245, d243837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23246 q = 1) (hb : d241832 q = 1) : d243838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23246, d243838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23246, d243838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23247 q = 1) (hb : d241832 q = 1) : d243839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23247, d243839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23247, d243839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23248 q = 1) (hb : d241832 q = 1) : d243840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23248, d243840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23248, d243840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60634 (p : Pattern) (ha : d23268 p = 1) (hb : d241832 p = 1) : d243846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23265 q = 1) (hb : d241832 q = 1) : d243843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23265, d243843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23265, d243843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23266 q = 1) (hb : d241832 q = 1) : d243844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23266, d243844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23266, d243844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23267 q = 1) (hb : d241832 q = 1) : d243845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23267, d243845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23267, d243845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23268 q = 1) (hb : d241832 q = 1) : d243846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23268, d243846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23268, d243846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60635 (p : Pattern) (ha : d211124 p = 1) (hb : d241832 p = 1) : d243852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d241832 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23218 q = 1) (hb : d241832 q = 1) : d243818 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23218, d243818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60628 q ha hb
    | true =>
      simp only [d23218, d243818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23219 q = 1) (hb : d241832 q = 1) : d243819 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23219, d243819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23219, d243819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23220 q = 1) (hb : d241832 q = 1) : d243820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23220, d243820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23220, d243820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23221 q = 1) (hb : d241832 q = 1) : d243821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23221, d243821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23221, d243821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d241832 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23225 q = 1) (hb : d241832 q = 1) : d243825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23225, d243825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60629 q ha hb
    | true =>
      simp only [d23225, d243825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23226 q = 1) (hb : d241832 q = 1) : d243826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23226, d243826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23226, d243826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23227 q = 1) (hb : d241832 q = 1) : d243827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23227, d243827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23227, d243827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23249 q = 1) (hb : d241832 q = 1) : d243841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23249, d243841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60633 q ha hb
    | true =>
      simp only [d23249, d243841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60615 q ha hb
  have h11 (q : Pattern) (ha : d211120 q = 1) (hb : d241832 q = 1) : d243842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d243842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211120, d243842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23269 q = 1) (hb : d241832 q = 1) : d243847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23269, d243847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60634 q ha hb
    | true =>
      simp only [d23269, d243847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23270 q = 1) (hb : d241832 q = 1) : d243848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23270, d243848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23270, d243848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d211121 q = 1) (hb : d241832 q = 1) : d243849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d243849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211121, d243849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211122 q = 1) (hb : d241832 q = 1) : d243850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d243850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211122, d243850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d211123 q = 1) (hb : d241832 q = 1) : d243851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d243851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211123, d243851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211124 q = 1) (hb : d241832 q = 1) : d243852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211124, d243852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211124, d243852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro60636 (p : Pattern) (ha : d23275 p = 1) (hb : d241832 p = 1) : d243853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d241832 q = 1) : d243744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23216 q = 1) (hb : d241832 q = 1) : d243816 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23216, d243816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23216, d243816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23275 q = 1) (hb : d241832 q = 1) : d243853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23275, d243853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23275, d243853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro60637 (p : Pattern) (ha : d23280 p = 1) (hb : d241832 p = 1) : d243858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23222 q = 1) (hb : d241832 q = 1) : d243822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23222, d243822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23222, d243822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23223 q = 1) (hb : d241832 q = 1) : d243823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23223, d243823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23223, d243823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23280 q = 1) (hb : d241832 q = 1) : d243858 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23280, d243858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23280, d243858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro60638 (p : Pattern) (ha : d23284 p = 1) (hb : d241832 p = 1) : d243862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23243 q = 1) (hb : d241832 q = 1) : d243835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23243, d243835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60632 q ha hb
    | true =>
      simp only [d23243, d243835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23244 q = 1) (hb : d241832 q = 1) : d243836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23244, d243836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23244, d243836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23245 q = 1) (hb : d241832 q = 1) : d243837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23245, d243837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23245, d243837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23246 q = 1) (hb : d241832 q = 1) : d243838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23246, d243838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23246, d243838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23247 q = 1) (hb : d241832 q = 1) : d243839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23247, d243839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23247, d243839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23284 q = 1) (hb : d241832 q = 1) : d243862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23284, d243862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23284, d243862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60639 (p : Pattern) (ha : d23289 p = 1) (hb : d241832 p = 1) : d243865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60614 q ha hb
    | true =>
      simp only [d23141, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23265 q = 1) (hb : d241832 q = 1) : d243843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23265, d243843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23265, d243843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23266 q = 1) (hb : d241832 q = 1) : d243844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23266, d243844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23266, d243844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23267 q = 1) (hb : d241832 q = 1) : d243845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23267, d243845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23267, d243845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23289 q = 1) (hb : d241832 q = 1) : d243865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23289, d243865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23289, d243865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60640 (p : Pattern) (ha : d211129 p = 1) (hb : d241832 p = 1) : d243871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d241832 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23218 q = 1) (hb : d241832 q = 1) : d243818 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23218, d243818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60628 q ha hb
    | true =>
      simp only [d23218, d243818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23219 q = 1) (hb : d241832 q = 1) : d243819 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23219, d243819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23219, d243819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23220 q = 1) (hb : d241832 q = 1) : d243820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23220, d243820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23220, d243820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23221 q = 1) (hb : d241832 q = 1) : d243821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23221, d243821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23221, d243821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d241832 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23225 q = 1) (hb : d241832 q = 1) : d243825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23225, d243825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60629 q ha hb
    | true =>
      simp only [d23225, d243825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23226 q = 1) (hb : d241832 q = 1) : d243826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23226, d243826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23226, d243826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23227 q = 1) (hb : d241832 q = 1) : d243827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23227, d243827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23227, d243827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23249 q = 1) (hb : d241832 q = 1) : d243841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23249, d243841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60633 q ha hb
    | true =>
      simp only [d23249, d243841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60615 q ha hb
  have h11 (q : Pattern) (ha : d211120 q = 1) (hb : d241832 q = 1) : d243842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d243842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211120, d243842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23269 q = 1) (hb : d241832 q = 1) : d243847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23269, d243847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60634 q ha hb
    | true =>
      simp only [d23269, d243847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23270 q = 1) (hb : d241832 q = 1) : d243848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23270, d243848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23270, d243848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d211121 q = 1) (hb : d241832 q = 1) : d243849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d243849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211121, d243849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211122 q = 1) (hb : d241832 q = 1) : d243850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d243850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211122, d243850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d211123 q = 1) (hb : d241832 q = 1) : d243851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d243851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211123, d243851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d241832 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d23276 q = 1) (hb : d241832 q = 1) : d243854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23276, d243854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60636 q ha hb
    | true =>
      simp only [d23276, d243854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23277 q = 1) (hb : d241832 q = 1) : d243855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23277, d243855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23277, d243855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d23278 q = 1) (hb : d241832 q = 1) : d243856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23278, d243856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23278, d243856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d23279 q = 1) (hb : d241832 q = 1) : d243857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23279, d243857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23279, d243857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d241832 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d23281 q = 1) (hb : d241832 q = 1) : d243859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23281, d243859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60637 q ha hb
    | true =>
      simp only [d23281, d243859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d23282 q = 1) (hb : d241832 q = 1) : d243860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23282, d243860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23282, d243860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d23283 q = 1) (hb : d241832 q = 1) : d243861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23283, d243861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23283, d243861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23285 q = 1) (hb : d241832 q = 1) : d243863 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23285, d243863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60638 q ha hb
    | true =>
      simp only [d23285, d243863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60617 q ha hb
  have h27 (q : Pattern) (ha : d211125 q = 1) (hb : d241832 q = 1) : d243864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d243864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d211125, d243864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d23290 q = 1) (hb : d241832 q = 1) : d243866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23290, d243866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60639 q ha hb
    | true =>
      simp only [d23290, d243866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d23291 q = 1) (hb : d241832 q = 1) : d243867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23291, d243867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d23291, d243867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d211126 q = 1) (hb : d241832 q = 1) : d243868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d243868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d211126, d243868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d211127 q = 1) (hb : d241832 q = 1) : d243869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211127, d243869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d211127, d243869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d211128 q = 1) (hb : d241832 q = 1) : d243870 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211128, d243870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211128, d243870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d211129 q = 1) (hb : d241832 q = 1) : d243871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211129, d243871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211129, d243871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro60641 (p : Pattern) (ha : d211136 p = 1) (hb : d241832 p = 1) : d243880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23285 q = 1) (hb : d241832 q = 1) : d243863 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23285, d243863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60638 q ha hb
    | true =>
      simp only [d23285, d243863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60617 q ha hb
  have h2 (q : Pattern) (ha : d211125 q = 1) (hb : d241832 q = 1) : d243864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d243864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211125, d243864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23290 q = 1) (hb : d241832 q = 1) : d243866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23290, d243866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60639 q ha hb
    | true =>
      simp only [d23290, d243866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23291 q = 1) (hb : d241832 q = 1) : d243867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23291, d243867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23291, d243867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211126 q = 1) (hb : d241832 q = 1) : d243868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d243868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211126, d243868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211134 q = 1) (hb : d241832 q = 1) : d243878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211134, d243878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211134, d243878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211135 q = 1) (hb : d241832 q = 1) : d243879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211135, d243879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211135, d243879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211136 q = 1) (hb : d241832 q = 1) : d243880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211136, d243880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211136, d243880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60642 (p : Pattern) (ha : d23315 p = 1) (hb : d241832 p = 1) : d243886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12599 q = 1) (hb : d241832 q = 1) : d30852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
  have h8 (q : Pattern) (ha : d9382 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
    | true =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12600 q = 1) (hb : d241832 q = 1) : d30853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12600, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9384 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12601 q = 1) (hb : d241832 q = 1) : d30854 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12601, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12602 q = 1) (hb : d241832 q = 1) : d30855 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12602, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23314 q = 1) (hb : d241832 q = 1) : d31131 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d31131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23314, d31131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69 q = 1) (hb : d241832 q = 1) : d69 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12603 q = 1) (hb : d241832 q = 1) : d30856 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d30856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12603, d30856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23315 q = 1) (hb : d241832 q = 1) : d243886 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23315, d243886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23315, d243886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro60643 (p : Pattern) (ha : d23321 p = 1) (hb : d241832 p = 1) : d243892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23316 q = 1) (hb : d241832 q = 1) : d243887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60642 q ha hb
    | true =>
      simp only [d23316, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60620 q ha hb
  have h2 (q : Pattern) (ha : d23317 q = 1) (hb : d241832 q = 1) : d243888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23318 q = 1) (hb : d241832 q = 1) : d243889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23172 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60620 q ha hb
    | true =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23173 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23174 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23319 q = 1) (hb : d241832 q = 1) : d243890 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23319, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d241832 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23175 q = 1) (hb : d241832 q = 1) : d243775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23175, d243775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23175, d243775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23320 q = 1) (hb : d241832 q = 1) : d243891 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23320, d243891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23320, d243891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23321 q = 1) (hb : d241832 q = 1) : d243892 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23321, d243892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23321, d243892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro60644 (p : Pattern) (ha : d23327 p = 1) (hb : d241832 p = 1) : d243898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23322 q = 1) (hb : d241832 q = 1) : d243893 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23322, d243893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60643 q ha hb
    | true =>
      simp only [d23322, d243893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23323 q = 1) (hb : d241832 q = 1) : d243894 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23323, d243894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23323, d243894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23178 q = 1) (hb : d241832 q = 1) : d243778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60621 q ha hb
    | true =>
      simp only [d23178, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23179 q = 1) (hb : d241832 q = 1) : d243779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23324 q = 1) (hb : d241832 q = 1) : d243895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23324, d243895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23324, d243895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23325 q = 1) (hb : d241832 q = 1) : d243896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23325, d243896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23325, d243896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23326 q = 1) (hb : d241832 q = 1) : d243897 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23326, d243897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23326, d243897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23327 q = 1) (hb : d241832 q = 1) : d243898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23327, d243898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23327, d243898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60645 (p : Pattern) (ha : d23347 p = 1) (hb : d241832 p = 1) : d243904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23178 q = 1) (hb : d241832 q = 1) : d243778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60621 q ha hb
    | true =>
      simp only [d23178, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23179 q = 1) (hb : d241832 q = 1) : d243779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23344 q = 1) (hb : d241832 q = 1) : d243901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23344, d243901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23344, d243901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23345 q = 1) (hb : d241832 q = 1) : d243902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23345, d243902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23345, d243902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23346 q = 1) (hb : d241832 q = 1) : d243903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23346, d243903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23346, d243903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23347 q = 1) (hb : d241832 q = 1) : d243904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23347, d243904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23347, d243904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60646 (p : Pattern) (ha : d211146 p = 1) (hb : d241832 p = 1) : d243910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23328 q = 1) (hb : d241832 q = 1) : d243899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23328, d243899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60644 q ha hb
    | true =>
      simp only [d23328, d243899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60622 q ha hb
  have h2 (q : Pattern) (ha : d211142 q = 1) (hb : d241832 q = 1) : d243900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211142, d243900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211142, d243900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23348 q = 1) (hb : d241832 q = 1) : d243905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23348, d243905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60645 q ha hb
    | true =>
      simp only [d23348, d243905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23349 q = 1) (hb : d241832 q = 1) : d243906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23349, d243906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23349, d243906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211143 q = 1) (hb : d241832 q = 1) : d243907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211143, d243907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211143, d243907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211144 q = 1) (hb : d241832 q = 1) : d243908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211144, d243908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211144, d243908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211145 q = 1) (hb : d241832 q = 1) : d243909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211145, d243909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211145, d243909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211146 q = 1) (hb : d241832 q = 1) : d243910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211146, d243910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211146, d243910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60647 (p : Pattern) (ha : d211152 p = 1) (hb : d241832 p = 1) : d243916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23206 q = 1) (hb : d241832 q = 1) : d243806 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23206, d243806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23206, d243806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60625 q ha hb
  have h2 (q : Pattern) (ha : d23207 q = 1) (hb : d241832 q = 1) : d243807 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23207, d243807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23207, d243807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23213 q = 1) (hb : d241832 q = 1) : d243813 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60625 q ha hb
    | true =>
      simp only [d23213, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60626 q ha hb
  have h4 (q : Pattern) (ha : d23214 q = 1) (hb : d241832 q = 1) : d243814 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23214, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23215 q = 1) (hb : d241832 q = 1) : d243815 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23215, d243815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23215, d243815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211130 q = 1) (hb : d241832 q = 1) : d243872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211130, d243872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60635 q ha hb
    | true =>
      simp only [d211130, d243872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60640 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d241832 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23298 q = 1) (hb : d241832 q = 1) : d243874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23298, d243874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60627 q ha hb
    | true =>
      simp only [d23298, d243874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211131 q = 1) (hb : d241832 q = 1) : d243875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211131, d243875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211131, d243875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211132 q = 1) (hb : d241832 q = 1) : d243876 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211132, d243876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211132, d243876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d211133 q = 1) (hb : d241832 q = 1) : d243877 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211133, d243877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211133, d243877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d211137 q = 1) (hb : d241832 q = 1) : d243881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211137, d243881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211137, d243881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60641 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d241832 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d211138 q = 1) (hb : d241832 q = 1) : d243882 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211138, d243882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211138, d243882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211139 q = 1) (hb : d241832 q = 1) : d243883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211139, d243883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211139, d243883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d211140 q = 1) (hb : d241832 q = 1) : d243884 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211140, d243884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211140, d243884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d211141 q = 1) (hb : d241832 q = 1) : d243885 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211141, d243885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211141, d243885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211147 q = 1) (hb : d241832 q = 1) : d243911 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211147, d243911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211147, d243911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60646 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d241832 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d211148 q = 1) (hb : d241832 q = 1) : d243912 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211148, d243912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d211148, d243912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d211149 q = 1) (hb : d241832 q = 1) : d243913 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211149, d243913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211149, d243913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d211150 q = 1) (hb : d241832 q = 1) : d243914 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211150, d243914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211150, d243914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d211151 q = 1) (hb : d241832 q = 1) : d243915 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211151, d243915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d211151, d243915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d211152 q = 1) (hb : d241832 q = 1) : d243916 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211152, d243916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211152, d243916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro60648 (p : Pattern) (ha : d211158 p = 1) (hb : d241832 p = 1) : d243922 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d241832 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211115 q = 1) (hb : d241832 q = 1) : d243796 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211115, d243796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211115, d243796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60624 q ha hb
  have h3 (q : Pattern) (ha : d211116 q = 1) (hb : d241832 q = 1) : d243797 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211116, d243797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211116, d243797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211117 q = 1) (hb : d241832 q = 1) : d243798 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211117, d243798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211117, d243798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211118 q = 1) (hb : d241832 q = 1) : d243799 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211118, d243799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211118, d243799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211119 q = 1) (hb : d241832 q = 1) : d243800 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211119, d243800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211119, d243800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211153 q = 1) (hb : d241832 q = 1) : d243917 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211153, d243917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211153, d243917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60647 q ha hb
  have h8 (q : Pattern) (ha : d211154 q = 1) (hb : d241832 q = 1) : d243918 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211154, d243918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211154, d243918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211155 q = 1) (hb : d241832 q = 1) : d243919 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211155, d243919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211155, d243919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211156 q = 1) (hb : d241832 q = 1) : d243920 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211156, d243920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211156, d243920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211157 q = 1) (hb : d241832 q = 1) : d243921 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211157, d243921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211157, d243921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d211158 q = 1) (hb : d241832 q = 1) : d243922 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211158, d243922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211158, d243922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro60649 (p : Pattern) (ha : d23368 p = 1) (hb : d241832 p = 1) : d243925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23237 q = 1) (hb : d241832 q = 1) : d243829 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60631 q ha hb
    | true =>
      simp only [d23237, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60613 q ha hb
  have h2 (q : Pattern) (ha : d23238 q = 1) (hb : d241832 q = 1) : d243830 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23239 q = 1) (hb : d241832 q = 1) : d243831 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23135 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60613 q ha hb
    | true =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23136 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23137 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23240 q = 1) (hb : d241832 q = 1) : d243832 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23240, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23366 q = 1) (hb : d241832 q = 1) : d243923 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23366, d243923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23366, d243923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23367 q = 1) (hb : d241832 q = 1) : d243924 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23367, d243924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23367, d243924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23368 q = 1) (hb : d241832 q = 1) : d243925 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23368, d243925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23368, d243925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro60650 (p : Pattern) (ha : d23372 p = 1) (hb : d241832 p = 1) : d243929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23135 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60613 q ha hb
    | true =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23136 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23137 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23366 q = 1) (hb : d241832 q = 1) : d243923 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23366, d243923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23366, d243923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23371 q = 1) (hb : d241832 q = 1) : d243928 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23371, d243928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23371, d243928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23372 q = 1) (hb : d241832 q = 1) : d243929 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23372, d243929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23372, d243929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro60651 (p : Pattern) (ha : d23378 p = 1) (hb : d241832 p = 1) : d243935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d241832 q = 1) : d243933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23377 q = 1) (hb : d241832 q = 1) : d243934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23377, d243934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23377, d243934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23378 q = 1) (hb : d241832 q = 1) : d243935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23378, d243935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23378, d243935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60652 (p : Pattern) (ha : d23382 p = 1) (hb : d241832 p = 1) : d243939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d241832 q = 1) : d243937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23381 q = 1) (hb : d241832 q = 1) : d243938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23381, d243938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23381, d243938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23382 q = 1) (hb : d241832 q = 1) : d243939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23382, d243939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23382, d243939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60653 (p : Pattern) (ha : d23388 p = 1) (hb : d241832 p = 1) : d243945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d241832 q = 1) : d243940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60651 q ha hb
    | true =>
      simp only [d23383, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60652 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d241832 q = 1) : d243941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d241832 q = 1) : d243942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d241832 q = 1) : d243943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d241832 q = 1) : d243944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23388 q = 1) (hb : d241832 q = 1) : d243945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60654 (p : Pattern) (ha : d23391 p = 1) (hb : d241832 p = 1) : d243948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d241832 q = 1) : d243933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23377 q = 1) (hb : d241832 q = 1) : d243934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23377, d243934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23377, d243934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23391 q = 1) (hb : d241832 q = 1) : d243948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23391, d243948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23391, d243948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60655 (p : Pattern) (ha : d23392 p = 1) (hb : d241832 p = 1) : d243949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d241832 q = 1) : d243937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23381 q = 1) (hb : d241832 q = 1) : d243938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23381, d243938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23381, d243938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23392 q = 1) (hb : d241832 q = 1) : d243949 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23392, d243949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23392, d243949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60656 (p : Pattern) (ha : d23398 p = 1) (hb : d241832 p = 1) : d243955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d241832 q = 1) : d243940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60651 q ha hb
    | true =>
      simp only [d23383, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60652 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d241832 q = 1) : d243941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d241832 q = 1) : d243942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d241832 q = 1) : d243943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d241832 q = 1) : d243944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23393 q = 1) (hb : d241832 q = 1) : d243950 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60654 q ha hb
    | true =>
      simp only [d23393, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60655 q ha hb
  have h7 (q : Pattern) (ha : d23394 q = 1) (hb : d241832 q = 1) : d243951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23394, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23395 q = 1) (hb : d241832 q = 1) : d243952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23395, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23396 q = 1) (hb : d241832 q = 1) : d243953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23397 q = 1) (hb : d241832 q = 1) : d243954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23398 q = 1) (hb : d241832 q = 1) : d243955 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23398, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro60657 (p : Pattern) (ha : d23513 p = 1) (hb : d241832 p = 1) : d244028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d241832 q = 1) : d243940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60651 q ha hb
    | true =>
      simp only [d23383, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60652 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d241832 q = 1) : d243941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d241832 q = 1) : d243942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d241832 q = 1) : d243943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d241832 q = 1) : d243944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23508 q = 1) (hb : d241832 q = 1) : d244023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23508, d244023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60652 q ha hb
    | true =>
      simp only [d23508, d244023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23509 q = 1) (hb : d241832 q = 1) : d244024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23509, d244024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23509, d244024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23510 q = 1) (hb : d241832 q = 1) : d244025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23510, d244025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23510, d244025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23511 q = 1) (hb : d241832 q = 1) : d244026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23511, d244026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23511, d244026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23512 q = 1) (hb : d241832 q = 1) : d244027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23512, d244027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23512, d244027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23513 q = 1) (hb : d241832 q = 1) : d244028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23513, d244028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23513, d244028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro60658 (p : Pattern) (ha : d23519 p = 1) (hb : d241832 p = 1) : d244034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23508 q = 1) (hb : d241832 q = 1) : d244023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23508, d244023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60652 q ha hb
    | true =>
      simp only [d23508, d244023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23509 q = 1) (hb : d241832 q = 1) : d244024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23509, d244024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23509, d244024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23510 q = 1) (hb : d241832 q = 1) : d244025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23510, d244025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23510, d244025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23511 q = 1) (hb : d241832 q = 1) : d244026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23511, d244026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23511, d244026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23512 q = 1) (hb : d241832 q = 1) : d244027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23512, d244027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23512, d244027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23514 q = 1) (hb : d241832 q = 1) : d244029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23514, d244029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60655 q ha hb
    | true =>
      simp only [d23514, d244029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23515 q = 1) (hb : d241832 q = 1) : d244030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23515, d244030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23515, d244030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23516 q = 1) (hb : d241832 q = 1) : d244031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23516, d244031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23516, d244031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23517 q = 1) (hb : d241832 q = 1) : d244032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23517, d244032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23517, d244032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23518 q = 1) (hb : d241832 q = 1) : d244033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23518, d244033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23518, d244033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23519 q = 1) (hb : d241832 q = 1) : d244034 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23519, d244034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23519, d244034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro60659 (p : Pattern) (ha : d23528 p = 1) (hb : d241832 p = 1) : d244043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23514 q = 1) (hb : d241832 q = 1) : d244029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23514, d244029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60655 q ha hb
    | true =>
      simp only [d23514, d244029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23515 q = 1) (hb : d241832 q = 1) : d244030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23515, d244030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23515, d244030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23516 q = 1) (hb : d241832 q = 1) : d244031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23516, d244031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23516, d244031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23517 q = 1) (hb : d241832 q = 1) : d244032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23517, d244032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23517, d244032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23518 q = 1) (hb : d241832 q = 1) : d244033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23518, d244033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23518, d244033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23528 q = 1) (hb : d241832 q = 1) : d244043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23528, d244043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23528, d244043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60660 (p : Pattern) (ha : d23558 p = 1) (hb : d241832 p = 1) : d244068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23172 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60620 q ha hb
    | true =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23173 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23174 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23548 q = 1) (hb : d241832 q = 1) : d244058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23548, d244058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23548, d244058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23557 q = 1) (hb : d241832 q = 1) : d244067 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23557, d244067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23557, d244067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23558 q = 1) (hb : d241832 q = 1) : d244068 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23558, d244068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23558, d244068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro60661 (p : Pattern) (ha : d23609 p = 1) (hb : d241832 p = 1) : d244091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23559 q = 1) (hb : d241832 q = 1) : d244069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23559, d244069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60660 q ha hb
    | true =>
      simp only [d23559, d244069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23560 q = 1) (hb : d241832 q = 1) : d244070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23560, d244070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23560, d244070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23606 q = 1) (hb : d241832 q = 1) : d244088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23606, d244088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23606, d244088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23607 q = 1) (hb : d241832 q = 1) : d244089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23607, d244089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23607, d244089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23608 q = 1) (hb : d241832 q = 1) : d244090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23608, d244090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23608, d244090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23609 q = 1) (hb : d241832 q = 1) : d244091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23609, d244091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23609, d244091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60662 (p : Pattern) (ha : d23615 p = 1) (hb : d241832 p = 1) : d244097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23610 q = 1) (hb : d241832 q = 1) : d244092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23610, d244092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60661 q ha hb
    | true =>
      simp only [d23610, d244092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23611 q = 1) (hb : d241832 q = 1) : d244093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23611, d244093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23611, d244093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23612 q = 1) (hb : d241832 q = 1) : d244094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23612, d244094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23612, d244094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23613 q = 1) (hb : d241832 q = 1) : d244095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23613, d244095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23613, d244095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23614 q = 1) (hb : d241832 q = 1) : d244096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23614, d244096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23614, d244096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23615 q = 1) (hb : d241832 q = 1) : d244097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23615, d244097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23615, d244097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60663 (p : Pattern) (ha : d23403 p = 1) (hb : d241832 p = 1) : d243960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d241832 q = 1) : d243933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23402 q = 1) (hb : d241832 q = 1) : d243959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23402, d243959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23402, d243959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23403 q = 1) (hb : d241832 q = 1) : d243960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23403, d243960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23403, d243960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60664 (p : Pattern) (ha : d23405 p = 1) (hb : d241832 p = 1) : d243962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d241832 q = 1) : d243937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23404 q = 1) (hb : d241832 q = 1) : d243961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23404, d243961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23404, d243961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23405 q = 1) (hb : d241832 q = 1) : d243962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23405, d243962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23405, d243962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60665 (p : Pattern) (ha : d23412 p = 1) (hb : d241832 p = 1) : d243969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23410 q = 1) (hb : d241832 q = 1) : d243967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23410, d243967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23410, d243967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23411 q = 1) (hb : d241832 q = 1) : d243968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23411, d243968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23411, d243968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23412 q = 1) (hb : d241832 q = 1) : d243969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23412, d243969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23412, d243969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60666 (p : Pattern) (ha : d23415 p = 1) (hb : d241832 p = 1) : d243972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23413 q = 1) (hb : d241832 q = 1) : d243970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23413, d243970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23413, d243970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23414 q = 1) (hb : d241832 q = 1) : d243971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23414, d243971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23414, d243971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23415 q = 1) (hb : d241832 q = 1) : d243972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23415, d243972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23415, d243972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60667 (p : Pattern) (ha : d23421 p = 1) (hb : d241832 p = 1) : d31325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d532 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d314 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d533 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d533, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23419 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23419, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23420 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23420, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d133 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d134 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d315 q = 1) (hb : d241831 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d241831, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315, d241831, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23228 q = 1) (hb : d241832 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23228, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d23229 q = 1) (hb : d241832 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23229, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h18 (q : Pattern) (ha : d23421 q = 1) (hb : d241832 q = 1) : d31325 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23421, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23421, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60668 (p : Pattern) (ha : d23427 p = 1) (hb : d241832 p = 1) : d243976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
    | true =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d241832 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d241832 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23233 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23234 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23426 q = 1) (hb : d241832 q = 1) : d31330 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23426, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
    | true =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d241832 q = 1) : d30761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d241832 q = 1) : d30762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23235 q = 1) (hb : d241832 q = 1) : d30994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d30994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23235, d30994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23427 q = 1) (hb : d241832 q = 1) : d243976 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23427, d243976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23427, d243976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60669 (p : Pattern) (ha : d23433 p = 1) (hb : d241832 p = 1) : d243982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23428 q = 1) (hb : d241832 q = 1) : d243977 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23428, d243977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60668 q ha hb
    | true =>
      simp only [d23428, d243977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60631 q ha hb
  have h2 (q : Pattern) (ha : d23429 q = 1) (hb : d241832 q = 1) : d243978 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23429, d243978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23429, d243978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23430 q = 1) (hb : d241832 q = 1) : d243979 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23430, d243979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23430, d243979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23237 q = 1) (hb : d241832 q = 1) : d243829 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60631 q ha hb
    | true =>
      simp only [d23237, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60613 q ha hb
  have h5 (q : Pattern) (ha : d23238 q = 1) (hb : d241832 q = 1) : d243830 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23239 q = 1) (hb : d241832 q = 1) : d243831 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23431 q = 1) (hb : d241832 q = 1) : d243980 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23431, d243980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23431, d243980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23135 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60613 q ha hb
    | true =>
      simp only [d23135, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23136 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23137 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23240 q = 1) (hb : d241832 q = 1) : d243832 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23240, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23432 q = 1) (hb : d241832 q = 1) : d243981 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23432, d243981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23432, d243981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23433 q = 1) (hb : d241832 q = 1) : d243982 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23433, d243982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23433, d243982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro60670 (p : Pattern) (ha : d23439 p = 1) (hb : d241832 p = 1) : d243988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23434 q = 1) (hb : d241832 q = 1) : d243983 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23434, d243983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60669 q ha hb
    | true =>
      simp only [d23434, d243983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23435 q = 1) (hb : d241832 q = 1) : d243984 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23435, d243984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23435, d243984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23436 q = 1) (hb : d241832 q = 1) : d243985 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23436, d243985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23436, d243985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23437 q = 1) (hb : d241832 q = 1) : d243986 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23437, d243986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23437, d243986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23438 q = 1) (hb : d241832 q = 1) : d243987 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23438, d243987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23438, d243987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23439 q = 1) (hb : d241832 q = 1) : d243988 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23439, d243988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23439, d243988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60671 (p : Pattern) (ha : d23476 p = 1) (hb : d241832 p = 1) : d243994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23473 q = 1) (hb : d241832 q = 1) : d243991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23473, d243991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23473, d243991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23474 q = 1) (hb : d241832 q = 1) : d243992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23474, d243992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23474, d243992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23475 q = 1) (hb : d241832 q = 1) : d243993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23475, d243993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23475, d243993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23476 q = 1) (hb : d241832 q = 1) : d243994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23476, d243994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23476, d243994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60672 (p : Pattern) (ha : d211163 p = 1) (hb : d241832 p = 1) : d244000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23406 q = 1) (hb : d241832 q = 1) : d243963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23406, d243963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60663 q ha hb
    | true =>
      simp only [d23406, d243963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60664 q ha hb
  have h2 (q : Pattern) (ha : d23407 q = 1) (hb : d241832 q = 1) : d243964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23407, d243964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23407, d243964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23408 q = 1) (hb : d241832 q = 1) : d243965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23408, d243965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23408, d243965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23409 q = 1) (hb : d241832 q = 1) : d243966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23409, d243966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23409, d243966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23416 q = 1) (hb : d241832 q = 1) : d243973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23416, d243973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60665 q ha hb
    | true =>
      simp only [d23416, d243973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60666 q ha hb
  have h6 (q : Pattern) (ha : d23417 q = 1) (hb : d241832 q = 1) : d243974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23417, d243974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23417, d243974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23418 q = 1) (hb : d241832 q = 1) : d243975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23418, d243975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23418, d243975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23440 q = 1) (hb : d241832 q = 1) : d243989 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23440, d243989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60670 q ha hb
    | true =>
      simp only [d23440, d243989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60651 q ha hb
  have h9 (q : Pattern) (ha : d211159 q = 1) (hb : d241832 q = 1) : d243990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d243990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211159, d243990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23477 q = 1) (hb : d241832 q = 1) : d243995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23477, d243995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60671 q ha hb
    | true =>
      simp only [d23477, d243995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23478 q = 1) (hb : d241832 q = 1) : d243996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23478, d243996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23478, d243996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d211160 q = 1) (hb : d241832 q = 1) : d243997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d243997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211160, d243997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211161 q = 1) (hb : d241832 q = 1) : d243998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d243998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211161, d243998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211162 q = 1) (hb : d241832 q = 1) : d243999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d243999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211162, d243999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211163 q = 1) (hb : d241832 q = 1) : d244000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211163, d244000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211163, d244000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60673 (p : Pattern) (ha : d23483 p = 1) (hb : d241832 p = 1) : d244001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d241832 q = 1) : d243933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23402 q = 1) (hb : d241832 q = 1) : d243959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23402, d243959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23402, d243959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23483 q = 1) (hb : d241832 q = 1) : d244001 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23483, d244001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23483, d244001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60674 (p : Pattern) (ha : d23484 p = 1) (hb : d241832 p = 1) : d244002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d241832 q = 1) : d243937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23404 q = 1) (hb : d241832 q = 1) : d243961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23404, d243961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23404, d243961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23484 q = 1) (hb : d241832 q = 1) : d244002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23484, d244002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23484, d244002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60675 (p : Pattern) (ha : d23489 p = 1) (hb : d241832 p = 1) : d244007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23410 q = 1) (hb : d241832 q = 1) : d243967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23410, d243967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23410, d243967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23411 q = 1) (hb : d241832 q = 1) : d243968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23411, d243968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23411, d243968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23489 q = 1) (hb : d241832 q = 1) : d244007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23489, d244007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23489, d244007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60676 (p : Pattern) (ha : d23490 p = 1) (hb : d241832 p = 1) : d244008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60650 q ha hb
    | true =>
      simp only [d23373, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23413 q = 1) (hb : d241832 q = 1) : d243970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23413, d243970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23413, d243970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23414 q = 1) (hb : d241832 q = 1) : d243971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23414, d243971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23414, d243971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23490 q = 1) (hb : d241832 q = 1) : d244008 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23490, d244008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23490, d244008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60677 (p : Pattern) (ha : d23494 p = 1) (hb : d241832 p = 1) : d244012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23434 q = 1) (hb : d241832 q = 1) : d243983 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23434, d243983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60669 q ha hb
    | true =>
      simp only [d23434, d243983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23435 q = 1) (hb : d241832 q = 1) : d243984 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23435, d243984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23435, d243984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23436 q = 1) (hb : d241832 q = 1) : d243985 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23436, d243985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23436, d243985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23437 q = 1) (hb : d241832 q = 1) : d243986 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23437, d243986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23437, d243986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23438 q = 1) (hb : d241832 q = 1) : d243987 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23438, d243987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23438, d243987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23494 q = 1) (hb : d241832 q = 1) : d244012 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23494, d244012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23494, d244012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60678 (p : Pattern) (ha : d23500 p = 1) (hb : d241832 p = 1) : d244015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60649 q ha hb
    | true =>
      simp only [d23369, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23473 q = 1) (hb : d241832 q = 1) : d243991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23473, d243991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23473, d243991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23474 q = 1) (hb : d241832 q = 1) : d243992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23474, d243992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23474, d243992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23475 q = 1) (hb : d241832 q = 1) : d243993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23475, d243993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23475, d243993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23500 q = 1) (hb : d241832 q = 1) : d244015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23500, d244015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23500, d244015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60679 (p : Pattern) (ha : d211168 p = 1) (hb : d241832 p = 1) : d244021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23406 q = 1) (hb : d241832 q = 1) : d243963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23406, d243963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60663 q ha hb
    | true =>
      simp only [d23406, d243963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60664 q ha hb
  have h2 (q : Pattern) (ha : d23407 q = 1) (hb : d241832 q = 1) : d243964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23407, d243964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23407, d243964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23408 q = 1) (hb : d241832 q = 1) : d243965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23408, d243965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23408, d243965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23409 q = 1) (hb : d241832 q = 1) : d243966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23409, d243966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23409, d243966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23416 q = 1) (hb : d241832 q = 1) : d243973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23416, d243973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60665 q ha hb
    | true =>
      simp only [d23416, d243973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60666 q ha hb
  have h6 (q : Pattern) (ha : d23417 q = 1) (hb : d241832 q = 1) : d243974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23417, d243974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23417, d243974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23418 q = 1) (hb : d241832 q = 1) : d243975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23418, d243975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23418, d243975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23440 q = 1) (hb : d241832 q = 1) : d243989 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23440, d243989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60670 q ha hb
    | true =>
      simp only [d23440, d243989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60651 q ha hb
  have h9 (q : Pattern) (ha : d211159 q = 1) (hb : d241832 q = 1) : d243990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d243990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211159, d243990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23477 q = 1) (hb : d241832 q = 1) : d243995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23477, d243995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60671 q ha hb
    | true =>
      simp only [d23477, d243995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23478 q = 1) (hb : d241832 q = 1) : d243996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23478, d243996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23478, d243996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d211160 q = 1) (hb : d241832 q = 1) : d243997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d243997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211160, d243997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211161 q = 1) (hb : d241832 q = 1) : d243998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d243998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211161, d243998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211162 q = 1) (hb : d241832 q = 1) : d243999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d243999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211162, d243999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23485 q = 1) (hb : d241832 q = 1) : d244003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23485, d244003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60673 q ha hb
    | true =>
      simp only [d23485, d244003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60674 q ha hb
  have h16 (q : Pattern) (ha : d23486 q = 1) (hb : d241832 q = 1) : d244004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23486, d244004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23486, d244004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23487 q = 1) (hb : d241832 q = 1) : d244005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23487, d244005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23487, d244005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23488 q = 1) (hb : d241832 q = 1) : d244006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23488, d244006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23488, d244006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23491 q = 1) (hb : d241832 q = 1) : d244009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23491, d244009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60675 q ha hb
    | true =>
      simp only [d23491, d244009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60676 q ha hb
  have h20 (q : Pattern) (ha : d23492 q = 1) (hb : d241832 q = 1) : d244010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23492, d244010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23492, d244010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23493 q = 1) (hb : d241832 q = 1) : d244011 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23493, d244011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23493, d244011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23495 q = 1) (hb : d241832 q = 1) : d244013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23495, d244013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60677 q ha hb
    | true =>
      simp only [d23495, d244013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60654 q ha hb
  have h23 (q : Pattern) (ha : d211164 q = 1) (hb : d241832 q = 1) : d244014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d244014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d211164, d244014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d23501 q = 1) (hb : d241832 q = 1) : d244016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23501, d244016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60678 q ha hb
    | true =>
      simp only [d23501, d244016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d23502 q = 1) (hb : d241832 q = 1) : d244017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23502, d244017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23502, d244017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d211165 q = 1) (hb : d241832 q = 1) : d244018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d244018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211165, d244018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d211166 q = 1) (hb : d241832 q = 1) : d244019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211166, d244019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211166, d244019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d211167 q = 1) (hb : d241832 q = 1) : d244020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211167, d244020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d211167, d244020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d211168 q = 1) (hb : d241832 q = 1) : d244021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211168, d244021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211168, d244021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro60680 (p : Pattern) (ha : d211175 p = 1) (hb : d241832 p = 1) : d244041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23495 q = 1) (hb : d241832 q = 1) : d244013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23495, d244013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60677 q ha hb
    | true =>
      simp only [d23495, d244013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60654 q ha hb
  have h2 (q : Pattern) (ha : d211164 q = 1) (hb : d241832 q = 1) : d244014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d244014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211164, d244014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23501 q = 1) (hb : d241832 q = 1) : d244016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23501, d244016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60678 q ha hb
    | true =>
      simp only [d23501, d244016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23502 q = 1) (hb : d241832 q = 1) : d244017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23502, d244017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23502, d244017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211165 q = 1) (hb : d241832 q = 1) : d244018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d244018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211165, d244018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211173 q = 1) (hb : d241832 q = 1) : d244039 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211173, d244039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211173, d244039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211174 q = 1) (hb : d241832 q = 1) : d244040 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211174, d244040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211174, d244040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211175 q = 1) (hb : d241832 q = 1) : d244041 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211175, d244041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211175, d244041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60681 (p : Pattern) (ha : d23539 p = 1) (hb : d241832 p = 1) : d244049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23534 q = 1) (hb : d241832 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
  have h2 (q : Pattern) (ha : d23422 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
    | true =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23535 q = 1) (hb : d241832 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23535, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23423 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23536 q = 1) (hb : d241832 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23536, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23537 q = 1) (hb : d241832 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23537, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23310 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
  have h8 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23311 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23312 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23313 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23538 q = 1) (hb : d241832 q = 1) : d31488 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23538, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d241832 q = 1) : d30852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60612 q ha hb
    | true =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d241832 q = 1) : d30853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d241832 q = 1) : d30854 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d241832 q = 1) : d30855 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23314 q = 1) (hb : d241832 q = 1) : d31131 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d31131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23314, d31131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23539 q = 1) (hb : d241832 q = 1) : d244049 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23539, d244049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23539, d244049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro60682 (p : Pattern) (ha : d23545 p = 1) (hb : d241832 p = 1) : d244055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23540 q = 1) (hb : d241832 q = 1) : d244050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23540, d244050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60681 q ha hb
    | true =>
      simp only [d23540, d244050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60642 q ha hb
  have h2 (q : Pattern) (ha : d23541 q = 1) (hb : d241832 q = 1) : d244051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23541, d244051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23541, d244051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23542 q = 1) (hb : d241832 q = 1) : d244052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23542, d244052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23542, d244052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23316 q = 1) (hb : d241832 q = 1) : d243887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60642 q ha hb
    | true =>
      simp only [d23316, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60620 q ha hb
  have h5 (q : Pattern) (ha : d23317 q = 1) (hb : d241832 q = 1) : d243888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23318 q = 1) (hb : d241832 q = 1) : d243889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23543 q = 1) (hb : d241832 q = 1) : d244053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23543, d244053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23543, d244053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23172 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60620 q ha hb
    | true =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23173 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23174 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23319 q = 1) (hb : d241832 q = 1) : d243890 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23319, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23544 q = 1) (hb : d241832 q = 1) : d244054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23544, d244054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23544, d244054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23545 q = 1) (hb : d241832 q = 1) : d244055 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23545, d244055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23545, d244055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro60683 (p : Pattern) (ha : d23550 p = 1) (hb : d241832 p = 1) : d244060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23316 q = 1) (hb : d241832 q = 1) : d243887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60642 q ha hb
    | true =>
      simp only [d23316, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60620 q ha hb
  have h2 (q : Pattern) (ha : d23317 q = 1) (hb : d241832 q = 1) : d243888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23318 q = 1) (hb : d241832 q = 1) : d243889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23172 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60620 q ha hb
    | true =>
      simp only [d23172, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23173 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23174 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23319 q = 1) (hb : d241832 q = 1) : d243890 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23319, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23548 q = 1) (hb : d241832 q = 1) : d244058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23548, d244058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23548, d244058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23549 q = 1) (hb : d241832 q = 1) : d244059 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23549, d244059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23549, d244059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23550 q = 1) (hb : d241832 q = 1) : d244060 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23550, d244060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23550, d244060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro60684 (p : Pattern) (ha : d23556 p = 1) (hb : d241832 p = 1) : d244066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23546 q = 1) (hb : d241832 q = 1) : d244056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23546, d244056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60682 q ha hb
    | true =>
      simp only [d23546, d244056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23547 q = 1) (hb : d241832 q = 1) : d244057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23547, d244057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23547, d244057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23551 q = 1) (hb : d241832 q = 1) : d244061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60683 q ha hb
    | true =>
      simp only [d23551, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23552 q = 1) (hb : d241832 q = 1) : d244062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23553 q = 1) (hb : d241832 q = 1) : d244063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23553, d244063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23553, d244063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23554 q = 1) (hb : d241832 q = 1) : d244064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23554, d244064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23554, d244064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23555 q = 1) (hb : d241832 q = 1) : d244065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23555, d244065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23555, d244065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23556 q = 1) (hb : d241832 q = 1) : d244066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23556, d244066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23556, d244066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60685 (p : Pattern) (ha : d23564 p = 1) (hb : d241832 p = 1) : d244074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23551 q = 1) (hb : d241832 q = 1) : d244061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60683 q ha hb
    | true =>
      simp only [d23551, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23552 q = 1) (hb : d241832 q = 1) : d244062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23559 q = 1) (hb : d241832 q = 1) : d244069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23559, d244069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60660 q ha hb
    | true =>
      simp only [d23559, d244069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23560 q = 1) (hb : d241832 q = 1) : d244070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23560, d244070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23560, d244070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23561 q = 1) (hb : d241832 q = 1) : d244071 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23561, d244071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23561, d244071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23562 q = 1) (hb : d241832 q = 1) : d244072 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23562, d244072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23562, d244072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23563 q = 1) (hb : d241832 q = 1) : d244073 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23563, d244073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23563, d244073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23564 q = 1) (hb : d241832 q = 1) : d244074 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23564, d244074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23564, d244074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60686 (p : Pattern) (ha : d23598 p = 1) (hb : d241832 p = 1) : d244080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23551 q = 1) (hb : d241832 q = 1) : d244061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60683 q ha hb
    | true =>
      simp only [d23551, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23552 q = 1) (hb : d241832 q = 1) : d244062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23595 q = 1) (hb : d241832 q = 1) : d244077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23595, d244077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23595, d244077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23596 q = 1) (hb : d241832 q = 1) : d244078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23596, d244078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23596, d244078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23597 q = 1) (hb : d241832 q = 1) : d244079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23597, d244079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23597, d244079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23598 q = 1) (hb : d241832 q = 1) : d244080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23598, d244080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23598, d244080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60687 (p : Pattern) (ha : d211185 p = 1) (hb : d241832 p = 1) : d244086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23565 q = 1) (hb : d241832 q = 1) : d244075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23565, d244075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60684 q ha hb
    | true =>
      simp only [d23565, d244075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60685 q ha hb
  have h2 (q : Pattern) (ha : d211181 q = 1) (hb : d241832 q = 1) : d244076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211181, d244076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211181, d244076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23599 q = 1) (hb : d241832 q = 1) : d244081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23599, d244081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60686 q ha hb
    | true =>
      simp only [d23599, d244081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23600 q = 1) (hb : d241832 q = 1) : d244082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23600, d244082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23600, d244082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211182 q = 1) (hb : d241832 q = 1) : d244083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211182, d244083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211182, d244083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211183 q = 1) (hb : d241832 q = 1) : d244084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211183, d244084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211183, d244084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211184 q = 1) (hb : d241832 q = 1) : d244085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211184, d244085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211184, d244085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211185 q = 1) (hb : d241832 q = 1) : d244086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211185, d244086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211185, d244086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60688 (p : Pattern) (ha : d211191 p = 1) (hb : d241832 p = 1) : d244103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23389 q = 1) (hb : d241832 q = 1) : d243946 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23389, d243946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23389, d243946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60653 q ha hb
  have h2 (q : Pattern) (ha : d23390 q = 1) (hb : d241832 q = 1) : d243947 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23390, d243947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23390, d243947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23399 q = 1) (hb : d241832 q = 1) : d243956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60653 q ha hb
    | true =>
      simp only [d23399, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60656 q ha hb
  have h4 (q : Pattern) (ha : d23400 q = 1) (hb : d241832 q = 1) : d243957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23400, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23401 q = 1) (hb : d241832 q = 1) : d243958 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23401, d243958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23401, d243958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211169 q = 1) (hb : d241832 q = 1) : d244022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211169, d244022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60672 q ha hb
    | true =>
      simp only [d211169, d244022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60679 q ha hb
  have h7 (q : Pattern) (ha : d23520 q = 1) (hb : d241832 q = 1) : d244035 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23520, d244035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60657 q ha hb
    | true =>
      simp only [d23520, d244035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60658 q ha hb
  have h8 (q : Pattern) (ha : d211170 q = 1) (hb : d241832 q = 1) : d244036 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211170, d244036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211170, d244036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211171 q = 1) (hb : d241832 q = 1) : d244037 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211171, d244037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211171, d244037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d211172 q = 1) (hb : d241832 q = 1) : d244038 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211172, d244038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211172, d244038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211176 q = 1) (hb : d241832 q = 1) : d244042 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211176, d244042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211176, d244042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60680 q ha hb
  have h12 (q : Pattern) (ha : d23529 q = 1) (hb : d241832 q = 1) : d244044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23529, d244044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23529, d244044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60659 q ha hb
  have h13 (q : Pattern) (ha : d211177 q = 1) (hb : d241832 q = 1) : d244045 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211177, d244045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211177, d244045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211178 q = 1) (hb : d241832 q = 1) : d244046 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211178, d244046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211178, d244046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d211179 q = 1) (hb : d241832 q = 1) : d244047 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211179, d244047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211179, d244047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d211180 q = 1) (hb : d241832 q = 1) : d244048 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211180, d244048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211180, d244048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211186 q = 1) (hb : d241832 q = 1) : d244087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211186, d244087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211186, d244087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60687 q ha hb
  have h18 (q : Pattern) (ha : d23616 q = 1) (hb : d241832 q = 1) : d244098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23616, d244098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23616, d244098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60662 q ha hb
  have h19 (q : Pattern) (ha : d211187 q = 1) (hb : d241832 q = 1) : d244099 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211187, d244099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211187, d244099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d211188 q = 1) (hb : d241832 q = 1) : d244100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211188, d244100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d211188, d244100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d211189 q = 1) (hb : d241832 q = 1) : d244101 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211189, d244101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211189, d244101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d211190 q = 1) (hb : d241832 q = 1) : d244102 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211190, d244102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211190, d244102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d211191 q = 1) (hb : d241832 q = 1) : d244103 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211191, d244103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211191, d244103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro60689 (p : Pattern) (ha : d211197 p = 1) (hb : d241832 p = 1) : d244109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211192 q = 1) (hb : d241832 q = 1) : d244104 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211192, d244104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211192, d244104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60688 q ha hb
  have h2 (q : Pattern) (ha : d211193 q = 1) (hb : d241832 q = 1) : d244105 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211193, d244105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211193, d244105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211194 q = 1) (hb : d241832 q = 1) : d244106 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211194, d244106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211194, d244106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211195 q = 1) (hb : d241832 q = 1) : d244107 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211195, d244107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211195, d244107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211196 q = 1) (hb : d241832 q = 1) : d244108 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211196, d244108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211196, d244108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211197 q = 1) (hb : d241832 q = 1) : d244109 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211197, d244109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211197, d244109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60690 (p : Pattern) (ha : d5450 p = 1) (hb : d241832 p = 1) : d244111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d241830 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d135 q = 1) (hb : d241831 q = 1) : d30635 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d241831, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d135, d241831, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5448 q = 1) (hb : d241832 q = 1) : d30756 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5448, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5449 q = 1) (hb : d241832 q = 1) : d30757 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5449, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5450 q = 1) (hb : d241832 q = 1) : d244111 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5450, d244111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5450, d244111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro60691 (p : Pattern) (ha : d5457 p = 1) (hb : d241832 p = 1) : d244123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
    | true =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d241832 q = 1) : d244114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d241832 q = 1) : d244115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5455 q = 1) (hb : d241832 q = 1) : d244118 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5455, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5457 q = 1) (hb : d241832 q = 1) : d244123 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5457, d244123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5457, d244123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60692 (p : Pattern) (ha : d23630 p = 1) (hb : d241832 p = 1) : d244117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
    | true =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d241832 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d241832 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23233 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23234 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23426 q = 1) (hb : d241832 q = 1) : d31330 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23426, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5451 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
    | true =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5453 q = 1) (hb : d241832 q = 1) : d244114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5454 q = 1) (hb : d241832 q = 1) : d244115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5454, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23629 q = 1) (hb : d241832 q = 1) : d244116 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23629, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23629, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23630 q = 1) (hb : d241832 q = 1) : d244117 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23630, d244117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23630, d244117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60693 (p : Pattern) (ha : d23631 p = 1) (hb : d241832 p = 1) : d244119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5451 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
    | true =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5452 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5453 q = 1) (hb : d241832 q = 1) : d244114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5454 q = 1) (hb : d241832 q = 1) : d244115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5454, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23629 q = 1) (hb : d241832 q = 1) : d244116 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23629, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23629, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5455 q = 1) (hb : d241832 q = 1) : d244118 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5455, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23631 q = 1) (hb : d241832 q = 1) : d244119 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23631, d244119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23631, d244119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro60694 (p : Pattern) (ha : d23641 p = 1) (hb : d241832 p = 1) : d244130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23632 q = 1) (hb : d241832 q = 1) : d244120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23632, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60692 q ha hb
    | true =>
      simp only [d23632, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60693 q ha hb
  have h2 (q : Pattern) (ha : d23633 q = 1) (hb : d241832 q = 1) : d244121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23633, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23633, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23634 q = 1) (hb : d241832 q = 1) : d244122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23634, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23634, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23635 q = 1) (hb : d241832 q = 1) : d244124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60693 q ha hb
    | true =>
      simp only [d23635, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60691 q ha hb
  have h5 (q : Pattern) (ha : d23636 q = 1) (hb : d241832 q = 1) : d244125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23637 q = 1) (hb : d241832 q = 1) : d244126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23638 q = 1) (hb : d241832 q = 1) : d244127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23638, d244127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23638, d244127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23639 q = 1) (hb : d241832 q = 1) : d244128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23639, d244128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23639, d244128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23640 q = 1) (hb : d241832 q = 1) : d244129 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23640, d244129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23640, d244129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23641 q = 1) (hb : d241832 q = 1) : d244130 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23641, d244130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23641, d244130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro60695 (p : Pattern) (ha : d23645 p = 1) (hb : d241832 p = 1) : d244134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23635 q = 1) (hb : d241832 q = 1) : d244124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60693 q ha hb
    | true =>
      simp only [d23635, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60691 q ha hb
  have h2 (q : Pattern) (ha : d23636 q = 1) (hb : d241832 q = 1) : d244125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23637 q = 1) (hb : d241832 q = 1) : d244126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23639 q = 1) (hb : d241832 q = 1) : d244128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23639, d244128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23639, d244128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23644 q = 1) (hb : d241832 q = 1) : d244133 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23644, d244133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23644, d244133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23645 q = 1) (hb : d241832 q = 1) : d244134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23645, d244134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23645, d244134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60696 (p : Pattern) (ha : d23651 p = 1) (hb : d241832 p = 1) : d244140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d241832 q = 1) : d244138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23650 q = 1) (hb : d241832 q = 1) : d244139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23650, d244139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23650, d244139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23651 q = 1) (hb : d241832 q = 1) : d244140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23651, d244140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23651, d244140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60697 (p : Pattern) (ha : d23655 p = 1) (hb : d241832 p = 1) : d244144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d241832 q = 1) : d244142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23654 q = 1) (hb : d241832 q = 1) : d244143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23654, d244143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23654, d244143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23655 q = 1) (hb : d241832 q = 1) : d244144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23655, d244144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23655, d244144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60698 (p : Pattern) (ha : d23661 p = 1) (hb : d241832 p = 1) : d244150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d241832 q = 1) : d244145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60696 q ha hb
    | true =>
      simp only [d23656, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60697 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d241832 q = 1) : d244146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d241832 q = 1) : d244147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d241832 q = 1) : d244148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d241832 q = 1) : d244149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23661 q = 1) (hb : d241832 q = 1) : d244150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60699 (p : Pattern) (ha : d23664 p = 1) (hb : d241832 p = 1) : d244153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d241832 q = 1) : d244138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23650 q = 1) (hb : d241832 q = 1) : d244139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23650, d244139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23650, d244139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23664 q = 1) (hb : d241832 q = 1) : d244153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23664, d244153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23664, d244153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60700 (p : Pattern) (ha : d23665 p = 1) (hb : d241832 p = 1) : d244154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d241832 q = 1) : d244142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23654 q = 1) (hb : d241832 q = 1) : d244143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23654, d244143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23654, d244143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23665 q = 1) (hb : d241832 q = 1) : d244154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23665, d244154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23665, d244154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60701 (p : Pattern) (ha : d23671 p = 1) (hb : d241832 p = 1) : d244160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d241832 q = 1) : d244145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60696 q ha hb
    | true =>
      simp only [d23656, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60697 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d241832 q = 1) : d244146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d241832 q = 1) : d244147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d241832 q = 1) : d244148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d241832 q = 1) : d244149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23666 q = 1) (hb : d241832 q = 1) : d244155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60699 q ha hb
    | true =>
      simp only [d23666, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60700 q ha hb
  have h7 (q : Pattern) (ha : d23667 q = 1) (hb : d241832 q = 1) : d244156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23667, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23668 q = 1) (hb : d241832 q = 1) : d244157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23668, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23669 q = 1) (hb : d241832 q = 1) : d244158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23670 q = 1) (hb : d241832 q = 1) : d244159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23671 q = 1) (hb : d241832 q = 1) : d244160 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23671, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro60702 (p : Pattern) (ha : d23793 p = 1) (hb : d241832 p = 1) : d244234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d241832 q = 1) : d244145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60696 q ha hb
    | true =>
      simp only [d23656, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60697 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d241832 q = 1) : d244146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d241832 q = 1) : d244147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d241832 q = 1) : d244148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d241832 q = 1) : d244149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23788 q = 1) (hb : d241832 q = 1) : d244229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23788, d244229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60697 q ha hb
    | true =>
      simp only [d23788, d244229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23789 q = 1) (hb : d241832 q = 1) : d244230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23789, d244230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23789, d244230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23790 q = 1) (hb : d241832 q = 1) : d244231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23790, d244231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23790, d244231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23791 q = 1) (hb : d241832 q = 1) : d244232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23791, d244232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23791, d244232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23792 q = 1) (hb : d241832 q = 1) : d244233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23792, d244233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23792, d244233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23793 q = 1) (hb : d241832 q = 1) : d244234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23793, d244234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23793, d244234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro60703 (p : Pattern) (ha : d23799 p = 1) (hb : d241832 p = 1) : d244240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23788 q = 1) (hb : d241832 q = 1) : d244229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23788, d244229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60697 q ha hb
    | true =>
      simp only [d23788, d244229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23789 q = 1) (hb : d241832 q = 1) : d244230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23789, d244230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23789, d244230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23790 q = 1) (hb : d241832 q = 1) : d244231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23790, d244231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23790, d244231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23791 q = 1) (hb : d241832 q = 1) : d244232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23791, d244232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23791, d244232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23792 q = 1) (hb : d241832 q = 1) : d244233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23792, d244233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23792, d244233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23794 q = 1) (hb : d241832 q = 1) : d244235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23794, d244235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60700 q ha hb
    | true =>
      simp only [d23794, d244235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23795 q = 1) (hb : d241832 q = 1) : d244236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23795, d244236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23795, d244236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23796 q = 1) (hb : d241832 q = 1) : d244237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23796, d244237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23796, d244237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23797 q = 1) (hb : d241832 q = 1) : d244238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23797, d244238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23797, d244238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23798 q = 1) (hb : d241832 q = 1) : d244239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23798, d244239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23798, d244239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23799 q = 1) (hb : d241832 q = 1) : d244240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23799, d244240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23799, d244240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro60704 (p : Pattern) (ha : d23808 p = 1) (hb : d241832 p = 1) : d244249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23794 q = 1) (hb : d241832 q = 1) : d244235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23794, d244235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60700 q ha hb
    | true =>
      simp only [d23794, d244235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23795 q = 1) (hb : d241832 q = 1) : d244236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23795, d244236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23795, d244236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23796 q = 1) (hb : d241832 q = 1) : d244237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23796, d244237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23796, d244237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23797 q = 1) (hb : d241832 q = 1) : d244238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23797, d244238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23797, d244238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23798 q = 1) (hb : d241832 q = 1) : d244239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23798, d244239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23798, d244239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23808 q = 1) (hb : d241832 q = 1) : d244249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23808, d244249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23808, d244249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60705 (p : Pattern) (ha : d5501 p = 1) (hb : d241832 p = 1) : d244272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d241832 q = 1) : d244257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
    | true =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d241832 q = 1) : d244258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d241832 q = 1) : d244259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d241832 q = 1) : d244260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5499 q = 1) (hb : d241832 q = 1) : d244266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5501 q = 1) (hb : d241832 q = 1) : d244272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5501, d244272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5501, d244272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60706 (p : Pattern) (ha : d23825 p = 1) (hb : d241832 p = 1) : d244267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5495 q = 1) (hb : d241832 q = 1) : d244257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
  have h8 (q : Pattern) (ha : d5451 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
    | true =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5496 q = 1) (hb : d241832 q = 1) : d244258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5496, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5452 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5497 q = 1) (hb : d241832 q = 1) : d244259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5497, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5498 q = 1) (hb : d241832 q = 1) : d244260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5498, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23820 q = 1) (hb : d241832 q = 1) : d244261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23820, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23820, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5499 q = 1) (hb : d241832 q = 1) : d244266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23825 q = 1) (hb : d241832 q = 1) : d244267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23825, d244267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23825, d244267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60707 (p : Pattern) (ha : d23848 p = 1) (hb : d241832 p = 1) : d244291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23830 q = 1) (hb : d241832 q = 1) : d244273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60706 q ha hb
    | true =>
      simp only [d23830, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60705 q ha hb
  have h2 (q : Pattern) (ha : d23831 q = 1) (hb : d241832 q = 1) : d244274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23832 q = 1) (hb : d241832 q = 1) : d244275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23838 q = 1) (hb : d241832 q = 1) : d244281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23838, d244281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23838, d244281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23847 q = 1) (hb : d241832 q = 1) : d244290 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23847, d244290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23847, d244290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23848 q = 1) (hb : d241832 q = 1) : d244291 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23848, d244291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23848, d244291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60708 (p : Pattern) (ha : d23906 p = 1) (hb : d241832 p = 1) : d244314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23849 q = 1) (hb : d241832 q = 1) : d244292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23849, d244292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60707 q ha hb
    | true =>
      simp only [d23849, d244292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23850 q = 1) (hb : d241832 q = 1) : d244293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23850, d244293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23850, d244293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23903 q = 1) (hb : d241832 q = 1) : d244311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23903, d244311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23903, d244311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23904 q = 1) (hb : d241832 q = 1) : d244312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23904, d244312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23904, d244312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23905 q = 1) (hb : d241832 q = 1) : d244313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23905, d244313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23905, d244313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23906 q = 1) (hb : d241832 q = 1) : d244314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23906, d244314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23906, d244314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60709 (p : Pattern) (ha : d23912 p = 1) (hb : d241832 p = 1) : d244320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23907 q = 1) (hb : d241832 q = 1) : d244315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23907, d244315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60708 q ha hb
    | true =>
      simp only [d23907, d244315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23908 q = 1) (hb : d241832 q = 1) : d244316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23908, d244316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23908, d244316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23909 q = 1) (hb : d241832 q = 1) : d244317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23909, d244317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23909, d244317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23910 q = 1) (hb : d241832 q = 1) : d244318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23910, d244318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23910, d244318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23911 q = 1) (hb : d241832 q = 1) : d244319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23911, d244319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23911, d244319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23912 q = 1) (hb : d241832 q = 1) : d244320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23912, d244320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23912, d244320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60710 (p : Pattern) (ha : d23676 p = 1) (hb : d241832 p = 1) : d244165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d241832 q = 1) : d244138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23675 q = 1) (hb : d241832 q = 1) : d244164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23675, d244164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23675, d244164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23676 q = 1) (hb : d241832 q = 1) : d244165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23676, d244165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23676, d244165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60711 (p : Pattern) (ha : d23678 p = 1) (hb : d241832 p = 1) : d244167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d241832 q = 1) : d244142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23677 q = 1) (hb : d241832 q = 1) : d244166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23677, d244166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23677, d244166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23678 q = 1) (hb : d241832 q = 1) : d244167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23678, d244167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23678, d244167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60712 (p : Pattern) (ha : d23685 p = 1) (hb : d241832 p = 1) : d244174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23683 q = 1) (hb : d241832 q = 1) : d244172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23683, d244172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23683, d244172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23684 q = 1) (hb : d241832 q = 1) : d244173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23684, d244173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23684, d244173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23685 q = 1) (hb : d241832 q = 1) : d244174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23685, d244174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23685, d244174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60713 (p : Pattern) (ha : d23688 p = 1) (hb : d241832 p = 1) : d244177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23686 q = 1) (hb : d241832 q = 1) : d244175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23686, d244175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23686, d244175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23687 q = 1) (hb : d241832 q = 1) : d244176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23687, d244176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23687, d244176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23688 q = 1) (hb : d241832 q = 1) : d244177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23688, d244177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23688, d244177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60714 (p : Pattern) (ha : d23694 p = 1) (hb : d241832 p = 1) : d31755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d202304 q = 1) : d31303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48082 q ha hb
    | true =>
      simp only [d822, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d823 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d241830 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d241830, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d531, d241830, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d532 q = 1) (hb : d241830 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d824 q = 1) (hb : d241831 q = 1) : d31305 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d241831, d31305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d824, d241831, d31305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23692 q = 1) (hb : d241832 q = 1) : d31753 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23692, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23692, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23693 q = 1) (hb : d241832 q = 1) : d31754 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23693, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23693, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d531 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d532 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d313 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d314 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d533 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d533, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23419 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23419, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d23420 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23420, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h18 (q : Pattern) (ha : d23694 q = 1) (hb : d241832 q = 1) : d31755 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23694, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23694, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro60715 (p : Pattern) (ha : d23700 p = 1) (hb : d241832 p = 1) : d244182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23695 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60714 q ha hb
    | true =>
      simp only [d23695, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23696 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23696, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23697 q = 1) (hb : d241832 q = 1) : d31758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23697, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23697, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23698 q = 1) (hb : d241832 q = 1) : d31759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23698, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23698, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23422 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
    | true =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23423 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23424 q = 1) (hb : d241832 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23425 q = 1) (hb : d241832 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23425, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23699 q = 1) (hb : d241832 q = 1) : d244181 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23699, d244181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23699, d244181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23426 q = 1) (hb : d241832 q = 1) : d31330 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23426, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23700 q = 1) (hb : d241832 q = 1) : d244182 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23700, d244182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23700, d244182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60716 (p : Pattern) (ha : d23706 p = 1) (hb : d241832 p = 1) : d244188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23701 q = 1) (hb : d241832 q = 1) : d244183 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23701, d244183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60715 q ha hb
    | true =>
      simp only [d23701, d244183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60692 q ha hb
  have h2 (q : Pattern) (ha : d23702 q = 1) (hb : d241832 q = 1) : d244184 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23702, d244184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23702, d244184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23703 q = 1) (hb : d241832 q = 1) : d244185 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23703, d244185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23703, d244185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23632 q = 1) (hb : d241832 q = 1) : d244120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23632, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60692 q ha hb
    | true =>
      simp only [d23632, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60693 q ha hb
  have h5 (q : Pattern) (ha : d23633 q = 1) (hb : d241832 q = 1) : d244121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23633, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23633, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23634 q = 1) (hb : d241832 q = 1) : d244122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23634, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23634, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23704 q = 1) (hb : d241832 q = 1) : d244186 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23704, d244186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23704, d244186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23635 q = 1) (hb : d241832 q = 1) : d244124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60693 q ha hb
    | true =>
      simp only [d23635, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60691 q ha hb
  have h9 (q : Pattern) (ha : d23636 q = 1) (hb : d241832 q = 1) : d244125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23637 q = 1) (hb : d241832 q = 1) : d244126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23638 q = 1) (hb : d241832 q = 1) : d244127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23638, d244127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23638, d244127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23705 q = 1) (hb : d241832 q = 1) : d244187 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23705, d244187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23705, d244187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23706 q = 1) (hb : d241832 q = 1) : d244188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23706, d244188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23706, d244188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro60717 (p : Pattern) (ha : d23712 p = 1) (hb : d241832 p = 1) : d244194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23707 q = 1) (hb : d241832 q = 1) : d244189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23707, d244189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60716 q ha hb
    | true =>
      simp only [d23707, d244189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23708 q = 1) (hb : d241832 q = 1) : d244190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23708, d244190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23708, d244190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23709 q = 1) (hb : d241832 q = 1) : d244191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23709, d244191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23709, d244191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23710 q = 1) (hb : d241832 q = 1) : d244192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23710, d244192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23710, d244192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23711 q = 1) (hb : d241832 q = 1) : d244193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23711, d244193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23711, d244193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23712 q = 1) (hb : d241832 q = 1) : d244194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23712, d244194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23712, d244194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60718 (p : Pattern) (ha : d23756 p = 1) (hb : d241832 p = 1) : d244200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23753 q = 1) (hb : d241832 q = 1) : d244197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23753, d244197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23753, d244197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23754 q = 1) (hb : d241832 q = 1) : d244198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23754, d244198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23754, d244198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23755 q = 1) (hb : d241832 q = 1) : d244199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23755, d244199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23755, d244199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23756 q = 1) (hb : d241832 q = 1) : d244200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23756, d244200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23756, d244200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60719 (p : Pattern) (ha : d211203 p = 1) (hb : d241832 p = 1) : d244206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23679 q = 1) (hb : d241832 q = 1) : d244168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23679, d244168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60710 q ha hb
    | true =>
      simp only [d23679, d244168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60711 q ha hb
  have h2 (q : Pattern) (ha : d23680 q = 1) (hb : d241832 q = 1) : d244169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23680, d244169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23680, d244169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23681 q = 1) (hb : d241832 q = 1) : d244170 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23681, d244170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23681, d244170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23682 q = 1) (hb : d241832 q = 1) : d244171 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23682, d244171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23682, d244171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23689 q = 1) (hb : d241832 q = 1) : d244178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23689, d244178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60712 q ha hb
    | true =>
      simp only [d23689, d244178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60713 q ha hb
  have h6 (q : Pattern) (ha : d23690 q = 1) (hb : d241832 q = 1) : d244179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23690, d244179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23690, d244179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23691 q = 1) (hb : d241832 q = 1) : d244180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23691, d244180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23691, d244180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23713 q = 1) (hb : d241832 q = 1) : d244195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23713, d244195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60717 q ha hb
    | true =>
      simp only [d23713, d244195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60696 q ha hb
  have h9 (q : Pattern) (ha : d211199 q = 1) (hb : d241832 q = 1) : d244196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d244196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211199, d244196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23757 q = 1) (hb : d241832 q = 1) : d244201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23757, d244201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60718 q ha hb
    | true =>
      simp only [d23757, d244201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23758 q = 1) (hb : d241832 q = 1) : d244202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23758, d244202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23758, d244202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d211200 q = 1) (hb : d241832 q = 1) : d244203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d244203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211200, d244203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211201 q = 1) (hb : d241832 q = 1) : d244204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d244204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211201, d244204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211202 q = 1) (hb : d241832 q = 1) : d244205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d244205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211202, d244205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211203 q = 1) (hb : d241832 q = 1) : d244206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211203, d244206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211203, d244206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60720 (p : Pattern) (ha : d23763 p = 1) (hb : d241832 p = 1) : d244207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d241832 q = 1) : d244138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23675 q = 1) (hb : d241832 q = 1) : d244164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23675, d244164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23675, d244164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23763 q = 1) (hb : d241832 q = 1) : d244207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23763, d244207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23763, d244207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60721 (p : Pattern) (ha : d23764 p = 1) (hb : d241832 p = 1) : d244208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d241832 q = 1) : d244142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23677 q = 1) (hb : d241832 q = 1) : d244166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23677, d244166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23677, d244166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23764 q = 1) (hb : d241832 q = 1) : d244208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23764, d244208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23764, d244208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60722 (p : Pattern) (ha : d23769 p = 1) (hb : d241832 p = 1) : d244213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23683 q = 1) (hb : d241832 q = 1) : d244172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23683, d244172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23683, d244172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23684 q = 1) (hb : d241832 q = 1) : d244173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23684, d244173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23684, d244173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23769 q = 1) (hb : d241832 q = 1) : d244213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23769, d244213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23769, d244213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60723 (p : Pattern) (ha : d23770 p = 1) (hb : d241832 p = 1) : d244214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60695 q ha hb
    | true =>
      simp only [d23646, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23686 q = 1) (hb : d241832 q = 1) : d244175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23686, d244175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23686, d244175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23687 q = 1) (hb : d241832 q = 1) : d244176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23687, d244176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23687, d244176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23770 q = 1) (hb : d241832 q = 1) : d244214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23770, d244214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23770, d244214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60724 (p : Pattern) (ha : d23774 p = 1) (hb : d241832 p = 1) : d244218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23707 q = 1) (hb : d241832 q = 1) : d244189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23707, d244189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60716 q ha hb
    | true =>
      simp only [d23707, d244189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23708 q = 1) (hb : d241832 q = 1) : d244190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23708, d244190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23708, d244190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23709 q = 1) (hb : d241832 q = 1) : d244191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23709, d244191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23709, d244191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23710 q = 1) (hb : d241832 q = 1) : d244192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23710, d244192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23710, d244192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23711 q = 1) (hb : d241832 q = 1) : d244193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23711, d244193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23711, d244193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23774 q = 1) (hb : d241832 q = 1) : d244218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23774, d244218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23774, d244218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60725 (p : Pattern) (ha : d23780 p = 1) (hb : d241832 p = 1) : d244221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60694 q ha hb
    | true =>
      simp only [d23642, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23753 q = 1) (hb : d241832 q = 1) : d244197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23753, d244197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23753, d244197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23754 q = 1) (hb : d241832 q = 1) : d244198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23754, d244198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23754, d244198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23755 q = 1) (hb : d241832 q = 1) : d244199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23755, d244199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23755, d244199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23780 q = 1) (hb : d241832 q = 1) : d244221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23780, d244221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23780, d244221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60726 (p : Pattern) (ha : d211208 p = 1) (hb : d241832 p = 1) : d244227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23679 q = 1) (hb : d241832 q = 1) : d244168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23679, d244168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60710 q ha hb
    | true =>
      simp only [d23679, d244168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60711 q ha hb
  have h2 (q : Pattern) (ha : d23680 q = 1) (hb : d241832 q = 1) : d244169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23680, d244169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23680, d244169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23681 q = 1) (hb : d241832 q = 1) : d244170 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23681, d244170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23681, d244170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23682 q = 1) (hb : d241832 q = 1) : d244171 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23682, d244171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23682, d244171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23689 q = 1) (hb : d241832 q = 1) : d244178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23689, d244178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60712 q ha hb
    | true =>
      simp only [d23689, d244178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60713 q ha hb
  have h6 (q : Pattern) (ha : d23690 q = 1) (hb : d241832 q = 1) : d244179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23690, d244179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23690, d244179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23691 q = 1) (hb : d241832 q = 1) : d244180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23691, d244180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23691, d244180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23713 q = 1) (hb : d241832 q = 1) : d244195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23713, d244195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60717 q ha hb
    | true =>
      simp only [d23713, d244195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60696 q ha hb
  have h9 (q : Pattern) (ha : d211199 q = 1) (hb : d241832 q = 1) : d244196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d244196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211199, d244196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23757 q = 1) (hb : d241832 q = 1) : d244201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23757, d244201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60718 q ha hb
    | true =>
      simp only [d23757, d244201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23758 q = 1) (hb : d241832 q = 1) : d244202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23758, d244202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23758, d244202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d211200 q = 1) (hb : d241832 q = 1) : d244203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d244203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211200, d244203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211201 q = 1) (hb : d241832 q = 1) : d244204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d244204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211201, d244204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211202 q = 1) (hb : d241832 q = 1) : d244205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d244205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211202, d244205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23765 q = 1) (hb : d241832 q = 1) : d244209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23765, d244209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60720 q ha hb
    | true =>
      simp only [d23765, d244209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60721 q ha hb
  have h16 (q : Pattern) (ha : d23766 q = 1) (hb : d241832 q = 1) : d244210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23766, d244210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23766, d244210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23767 q = 1) (hb : d241832 q = 1) : d244211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23767, d244211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23767, d244211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23768 q = 1) (hb : d241832 q = 1) : d244212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23768, d244212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23768, d244212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23771 q = 1) (hb : d241832 q = 1) : d244215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23771, d244215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60722 q ha hb
    | true =>
      simp only [d23771, d244215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60723 q ha hb
  have h20 (q : Pattern) (ha : d23772 q = 1) (hb : d241832 q = 1) : d244216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23772, d244216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23772, d244216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23773 q = 1) (hb : d241832 q = 1) : d244217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23773, d244217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23773, d244217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23775 q = 1) (hb : d241832 q = 1) : d244219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23775, d244219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60724 q ha hb
    | true =>
      simp only [d23775, d244219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60699 q ha hb
  have h23 (q : Pattern) (ha : d211204 q = 1) (hb : d241832 q = 1) : d244220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d244220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d211204, d244220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d23781 q = 1) (hb : d241832 q = 1) : d244222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23781, d244222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60725 q ha hb
    | true =>
      simp only [d23781, d244222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d23782 q = 1) (hb : d241832 q = 1) : d244223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23782, d244223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23782, d244223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d211205 q = 1) (hb : d241832 q = 1) : d244224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d244224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211205, d244224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d211206 q = 1) (hb : d241832 q = 1) : d244225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211206, d244225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211206, d244225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d211207 q = 1) (hb : d241832 q = 1) : d244226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211207, d244226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d211207, d244226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d211208 q = 1) (hb : d241832 q = 1) : d244227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211208, d244227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211208, d244227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro60727 (p : Pattern) (ha : d211215 p = 1) (hb : d241832 p = 1) : d244247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23775 q = 1) (hb : d241832 q = 1) : d244219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23775, d244219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60724 q ha hb
    | true =>
      simp only [d23775, d244219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60699 q ha hb
  have h2 (q : Pattern) (ha : d211204 q = 1) (hb : d241832 q = 1) : d244220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d244220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211204, d244220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23781 q = 1) (hb : d241832 q = 1) : d244222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23781, d244222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60725 q ha hb
    | true =>
      simp only [d23781, d244222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23782 q = 1) (hb : d241832 q = 1) : d244223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23782, d244223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23782, d244223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211205 q = 1) (hb : d241832 q = 1) : d244224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d244224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211205, d244224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211213 q = 1) (hb : d241832 q = 1) : d244245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211213, d244245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211213, d244245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211214 q = 1) (hb : d241832 q = 1) : d244246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211214, d244246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211214, d244246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211215 q = 1) (hb : d241832 q = 1) : d244247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211215, d244247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211215, d244247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60728 (p : Pattern) (ha : d23819 p = 1) (hb : d241832 p = 1) : d244256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23814 q = 1) (hb : d241832 q = 1) : d31957 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23814, d31957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23814, d31957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60714 q ha hb
  have h2 (q : Pattern) (ha : d23695 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60714 q ha hb
    | true =>
      simp only [d23695, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23815 q = 1) (hb : d241832 q = 1) : d31958 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23815, d31958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23815, d31958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23696 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23696, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23816 q = 1) (hb : d241832 q = 1) : d31959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23816, d31959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23816, d31959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23817 q = 1) (hb : d241832 q = 1) : d31960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23817, d31960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23817, d31960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23534 q = 1) (hb : d241832 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
  have h8 (q : Pattern) (ha : d23422 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
    | true =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23535 q = 1) (hb : d241832 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23535, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23423 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23536 q = 1) (hb : d241832 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23536, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23537 q = 1) (hb : d241832 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23537, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23818 q = 1) (hb : d241832 q = 1) : d244255 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23818, d244255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23818, d244255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23538 q = 1) (hb : d241832 q = 1) : d31488 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23538, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23819 q = 1) (hb : d241832 q = 1) : d244256 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23819, d244256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23819, d244256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro60729 (p : Pattern) (ha : d23821 p = 1) (hb : d241832 p = 1) : d244262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23534 q = 1) (hb : d241832 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
  have h2 (q : Pattern) (ha : d23422 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60667 q ha hb
    | true =>
      simp only [d23422, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23535 q = 1) (hb : d241832 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23535, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23423 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23423, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23536 q = 1) (hb : d241832 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23536, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23537 q = 1) (hb : d241832 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23537, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23310 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
  have h8 (q : Pattern) (ha : d23231 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60630 q ha hb
    | true =>
      simp only [d23231, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23311 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23311, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23232 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23232, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23312 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23312, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23313 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23313, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23538 q = 1) (hb : d241832 q = 1) : d31488 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23538, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5495 q = 1) (hb : d241832 q = 1) : d244257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
  have h15 (q : Pattern) (ha : d5451 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60690 q ha hb
    | true =>
      simp only [d5451, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5496 q = 1) (hb : d241832 q = 1) : d244258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5496, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5452 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5452, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5497 q = 1) (hb : d241832 q = 1) : d244259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5497, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5498 q = 1) (hb : d241832 q = 1) : d244260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5498, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23820 q = 1) (hb : d241832 q = 1) : d244261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23820, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23820, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23821 q = 1) (hb : d241832 q = 1) : d244262 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23821, d244262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23821, d244262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro60730 (p : Pattern) (ha : d23835 p = 1) (hb : d241832 p = 1) : d244278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23822 q = 1) (hb : d241832 q = 1) : d244263 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23822, d244263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60728 q ha hb
    | true =>
      simp only [d23822, d244263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60729 q ha hb
  have h2 (q : Pattern) (ha : d23823 q = 1) (hb : d241832 q = 1) : d244264 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23823, d244264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23823, d244264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23824 q = 1) (hb : d241832 q = 1) : d244265 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23824, d244265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23824, d244265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23826 q = 1) (hb : d241832 q = 1) : d244268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23826, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60729 q ha hb
    | true =>
      simp only [d23826, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60706 q ha hb
  have h5 (q : Pattern) (ha : d23827 q = 1) (hb : d241832 q = 1) : d244269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23827, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23827, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23828 q = 1) (hb : d241832 q = 1) : d244270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23828, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23828, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23829 q = 1) (hb : d241832 q = 1) : d244271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23829, d244271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23829, d244271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23830 q = 1) (hb : d241832 q = 1) : d244273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60706 q ha hb
    | true =>
      simp only [d23830, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60705 q ha hb
  have h9 (q : Pattern) (ha : d23831 q = 1) (hb : d241832 q = 1) : d244274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23832 q = 1) (hb : d241832 q = 1) : d244275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23833 q = 1) (hb : d241832 q = 1) : d244276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23833, d244276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23833, d244276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23834 q = 1) (hb : d241832 q = 1) : d244277 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23834, d244277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23834, d244277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23835 q = 1) (hb : d241832 q = 1) : d244278 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23835, d244278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23835, d244278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro60731 (p : Pattern) (ha : d23840 p = 1) (hb : d241832 p = 1) : d244283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23826 q = 1) (hb : d241832 q = 1) : d244268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23826, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60729 q ha hb
    | true =>
      simp only [d23826, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60706 q ha hb
  have h2 (q : Pattern) (ha : d23827 q = 1) (hb : d241832 q = 1) : d244269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23827, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23827, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23828 q = 1) (hb : d241832 q = 1) : d244270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23828, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23828, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23830 q = 1) (hb : d241832 q = 1) : d244273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60706 q ha hb
    | true =>
      simp only [d23830, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60705 q ha hb
  have h5 (q : Pattern) (ha : d23831 q = 1) (hb : d241832 q = 1) : d244274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23832 q = 1) (hb : d241832 q = 1) : d244275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23833 q = 1) (hb : d241832 q = 1) : d244276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23833, d244276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23833, d244276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23838 q = 1) (hb : d241832 q = 1) : d244281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23838, d244281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23838, d244281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23839 q = 1) (hb : d241832 q = 1) : d244282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23839, d244282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23839, d244282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23840 q = 1) (hb : d241832 q = 1) : d244283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23840, d244283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23840, d244283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro60732 (p : Pattern) (ha : d23846 p = 1) (hb : d241832 p = 1) : d244289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23836 q = 1) (hb : d241832 q = 1) : d244279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23836, d244279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60730 q ha hb
    | true =>
      simp only [d23836, d244279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23837 q = 1) (hb : d241832 q = 1) : d244280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23837, d244280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23837, d244280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23841 q = 1) (hb : d241832 q = 1) : d244284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60731 q ha hb
    | true =>
      simp only [d23841, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23842 q = 1) (hb : d241832 q = 1) : d244285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23843 q = 1) (hb : d241832 q = 1) : d244286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23843, d244286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23843, d244286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23844 q = 1) (hb : d241832 q = 1) : d244287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23844, d244287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23844, d244287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23845 q = 1) (hb : d241832 q = 1) : d244288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23845, d244288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23845, d244288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23846 q = 1) (hb : d241832 q = 1) : d244289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23846, d244289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23846, d244289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60733 (p : Pattern) (ha : d23854 p = 1) (hb : d241832 p = 1) : d244297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23841 q = 1) (hb : d241832 q = 1) : d244284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60731 q ha hb
    | true =>
      simp only [d23841, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23842 q = 1) (hb : d241832 q = 1) : d244285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23849 q = 1) (hb : d241832 q = 1) : d244292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23849, d244292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60707 q ha hb
    | true =>
      simp only [d23849, d244292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23850 q = 1) (hb : d241832 q = 1) : d244293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23850, d244293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23850, d244293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23851 q = 1) (hb : d241832 q = 1) : d244294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23851, d244294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23851, d244294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23852 q = 1) (hb : d241832 q = 1) : d244295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23852, d244295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23852, d244295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23853 q = 1) (hb : d241832 q = 1) : d244296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23853, d244296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23853, d244296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23854 q = 1) (hb : d241832 q = 1) : d244297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23854, d244297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23854, d244297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro60734 (p : Pattern) (ha : d23895 p = 1) (hb : d241832 p = 1) : d244303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23841 q = 1) (hb : d241832 q = 1) : d244284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60731 q ha hb
    | true =>
      simp only [d23841, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23842 q = 1) (hb : d241832 q = 1) : d244285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23892 q = 1) (hb : d241832 q = 1) : d244300 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23892, d244300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23892, d244300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23893 q = 1) (hb : d241832 q = 1) : d244301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23893, d244301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23893, d244301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23894 q = 1) (hb : d241832 q = 1) : d244302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23894, d244302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23894, d244302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23895 q = 1) (hb : d241832 q = 1) : d244303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23895, d244303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23895, d244303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60735 (p : Pattern) (ha : d211225 p = 1) (hb : d241832 p = 1) : d244309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23855 q = 1) (hb : d241832 q = 1) : d244298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23855, d244298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60732 q ha hb
    | true =>
      simp only [d23855, d244298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60733 q ha hb
  have h2 (q : Pattern) (ha : d211221 q = 1) (hb : d241832 q = 1) : d244299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211221, d244299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211221, d244299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23896 q = 1) (hb : d241832 q = 1) : d244304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23896, d244304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60734 q ha hb
    | true =>
      simp only [d23896, d244304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23897 q = 1) (hb : d241832 q = 1) : d244305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23897, d244305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23897, d244305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211222 q = 1) (hb : d241832 q = 1) : d244306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211222, d244306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211222, d244306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211223 q = 1) (hb : d241832 q = 1) : d244307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211223, d244307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211223, d244307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211224 q = 1) (hb : d241832 q = 1) : d244308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211224, d244308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211224, d244308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211225 q = 1) (hb : d241832 q = 1) : d244309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211225, d244309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211225, d244309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60736 (p : Pattern) (ha : d211231 p = 1) (hb : d241832 p = 1) : d244326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23662 q = 1) (hb : d241832 q = 1) : d244151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23662, d244151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23662, d244151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60698 q ha hb
  have h2 (q : Pattern) (ha : d23663 q = 1) (hb : d241832 q = 1) : d244152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23663, d244152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23663, d244152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23672 q = 1) (hb : d241832 q = 1) : d244161 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60698 q ha hb
    | true =>
      simp only [d23672, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60701 q ha hb
  have h4 (q : Pattern) (ha : d23673 q = 1) (hb : d241832 q = 1) : d244162 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23673, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23674 q = 1) (hb : d241832 q = 1) : d244163 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23674, d244163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23674, d244163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211209 q = 1) (hb : d241832 q = 1) : d244228 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211209, d244228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60719 q ha hb
    | true =>
      simp only [d211209, d244228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60726 q ha hb
  have h7 (q : Pattern) (ha : d23800 q = 1) (hb : d241832 q = 1) : d244241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23800, d244241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60702 q ha hb
    | true =>
      simp only [d23800, d244241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60703 q ha hb
  have h8 (q : Pattern) (ha : d211210 q = 1) (hb : d241832 q = 1) : d244242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211210, d244242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211210, d244242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211211 q = 1) (hb : d241832 q = 1) : d244243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211211, d244243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211211, d244243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d211212 q = 1) (hb : d241832 q = 1) : d244244 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211212, d244244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211212, d244244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211216 q = 1) (hb : d241832 q = 1) : d244248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211216, d244248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211216, d244248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60727 q ha hb
  have h12 (q : Pattern) (ha : d23809 q = 1) (hb : d241832 q = 1) : d244250 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23809, d244250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23809, d244250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60704 q ha hb
  have h13 (q : Pattern) (ha : d211217 q = 1) (hb : d241832 q = 1) : d244251 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211217, d244251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211217, d244251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211218 q = 1) (hb : d241832 q = 1) : d244252 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211218, d244252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211218, d244252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d211219 q = 1) (hb : d241832 q = 1) : d244253 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211219, d244253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211219, d244253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d211220 q = 1) (hb : d241832 q = 1) : d244254 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211220, d244254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211220, d244254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211226 q = 1) (hb : d241832 q = 1) : d244310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211226, d244310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211226, d244310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60735 q ha hb
  have h18 (q : Pattern) (ha : d23913 q = 1) (hb : d241832 q = 1) : d244321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23913, d244321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23913, d244321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60709 q ha hb
  have h19 (q : Pattern) (ha : d211227 q = 1) (hb : d241832 q = 1) : d244322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211227, d244322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211227, d244322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d211228 q = 1) (hb : d241832 q = 1) : d244323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211228, d244323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d211228, d244323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d211229 q = 1) (hb : d241832 q = 1) : d244324 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211229, d244324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211229, d244324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d211230 q = 1) (hb : d241832 q = 1) : d244325 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211230, d244325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211230, d244325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d211231 q = 1) (hb : d241832 q = 1) : d244326 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211231, d244326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211231, d244326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro60737 (p : Pattern) (ha : d211237 p = 1) (hb : d241832 p = 1) : d244332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211232 q = 1) (hb : d241832 q = 1) : d244327 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211232, d244327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211232, d244327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60736 q ha hb
  have h2 (q : Pattern) (ha : d211233 q = 1) (hb : d241832 q = 1) : d244328 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211233, d244328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211233, d244328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211234 q = 1) (hb : d241832 q = 1) : d244329 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211234, d244329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211234, d244329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211235 q = 1) (hb : d241832 q = 1) : d244330 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211235, d244330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211235, d244330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211236 q = 1) (hb : d241832 q = 1) : d244331 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211236, d244331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211236, d244331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211237 q = 1) (hb : d241832 q = 1) : d244332 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211237, d244332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211237, d244332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60738 (p : Pattern) (ha : d23931 p = 1) (hb : d241832 p = 1) : d31755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d202304 q = 1) : d31303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48082 q ha hb
    | true =>
      simp only [d822, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d823 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1087 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1088 q = 1) (hb : d241830 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d241830, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d1088, d241830, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1089 q = 1) (hb : d241830 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1089, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1090 q = 1) (hb : d241831 q = 1) : d31305 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d241831, d31305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1090, d241831, d31305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23927 q = 1) (hb : d241832 q = 1) : d31753 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23927, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23927, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d23928 q = 1) (hb : d241832 q = 1) : d31754 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23928, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23928, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1088 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d1088, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48048 q ha hb
  have h13 (q : Pattern) (ha : d1089 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1089, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1093 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1094 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d1094, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d1095 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1095, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h17 (q : Pattern) (ha : d1096 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1096, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23929 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23929, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d23929, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h19 (q : Pattern) (ha : d23930 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23930, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23930, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h20 (q : Pattern) (ha : d23931 q = 1) (hb : d241832 q = 1) : d31755 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23931, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23931, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro60739 (p : Pattern) (ha : d23938 p = 1) (hb : d241832 p = 1) : d31642 p = 1 := by
  have h0 (q : Pattern) (ha : d1088 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d1088, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48048 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1089 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1089, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1093 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1094 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d1094, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1095 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1095, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1096 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1096, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23929 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23929, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23929, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d23930 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23930, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23930, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1094 q = 1) (hb : d202304 q = 1) : d31621 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d31621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d1094, d31621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48050 q ha hb
  have h13 (q : Pattern) (ha : d1095 q = 1) (hb : d202304 q = 1) : d31622 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d31622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1095, d31622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1104 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d1104, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d1105 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1105, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h17 (q : Pattern) (ha : d1106 q = 1) (hb : d241831 q = 1) : d31633 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d241831, d31633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1106, d241831, d31633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23936 q = 1) (hb : d241832 q = 1) : d31634 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23936, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d23936, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h19 (q : Pattern) (ha : d23937 q = 1) (hb : d241832 q = 1) : d31635 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23937, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23937, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h20 (q : Pattern) (ha : d23938 q = 1) (hb : d241832 q = 1) : d31642 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23938, d31642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23938, d31642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro60740 (p : Pattern) (ha : d23944 p = 1) (hb : d241832 p = 1) : d244335 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d202304 q = 1) : d31621 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d31621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d1094, d31621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48050 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d202304 q = 1) : d31622 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d31622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d31622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1104 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d1104, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1105 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1105, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1106 q = 1) (hb : d241831 q = 1) : d31633 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d241831, d31633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1106, d241831, d31633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23936 q = 1) (hb : d241832 q = 1) : d31634 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23936, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23936, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d23937 q = 1) (hb : d241832 q = 1) : d31635 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23937, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23937, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5538 q = 1) (hb : d241832 q = 1) : d5538 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23944 q = 1) (hb : d241832 q = 1) : d244335 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23944, d244335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23944, d244335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro60741 (p : Pattern) (ha : d23950 p = 1) (hb : d241832 p = 1) : d244341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23932 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60738 q ha hb
    | true =>
      simp only [d23932, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23933 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23933, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23934 q = 1) (hb : d241832 q = 1) : d31758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23934, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23934, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23935 q = 1) (hb : d241832 q = 1) : d31759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23935, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23935, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23939 q = 1) (hb : d241832 q = 1) : d31643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60739 q ha hb
    | true =>
      simp only [d23939, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23940 q = 1) (hb : d241832 q = 1) : d31644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23940, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23941 q = 1) (hb : d241832 q = 1) : d31645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23942 q = 1) (hb : d241832 q = 1) : d31646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23942, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23943 q = 1) (hb : d241832 q = 1) : d31760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23943, d31760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23943, d31760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23945 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60740 q ha hb
    | true =>
      simp only [d23945, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23946 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23946, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23947 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23948 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23948, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23949 q = 1) (hb : d241832 q = 1) : d244340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23949, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23950 q = 1) (hb : d241832 q = 1) : d244341 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23950, d244341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23950, d244341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro60742 (p : Pattern) (ha : d23952 p = 1) (hb : d241832 p = 1) : d244343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23939 q = 1) (hb : d241832 q = 1) : d31643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60739 q ha hb
    | true =>
      simp only [d23939, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23940 q = 1) (hb : d241832 q = 1) : d31644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23940, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23941 q = 1) (hb : d241832 q = 1) : d31645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23942 q = 1) (hb : d241832 q = 1) : d31646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23942, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23945 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60740 q ha hb
    | true =>
      simp only [d23945, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23946 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23946, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23947 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23948 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23948, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23949 q = 1) (hb : d241832 q = 1) : d244340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23949, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23951 q = 1) (hb : d241832 q = 1) : d244342 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23951, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23951, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23952 q = 1) (hb : d241832 q = 1) : d244343 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23952, d244343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23952, d244343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro60743 (p : Pattern) (ha : d23956 p = 1) (hb : d241832 p = 1) : d244347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23945 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60740 q ha hb
    | true =>
      simp only [d23945, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23946 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23946, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23947 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23948 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23948, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23951 q = 1) (hb : d241832 q = 1) : d244342 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23951, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23951, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1140 q = 1) (hb : d241832 q = 1) : d1140 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23956 q = 1) (hb : d241832 q = 1) : d244347 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23956, d244347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23956, d244347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro60744 (p : Pattern) (ha : d23963 p = 1) (hb : d241832 p = 1) : d244354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23953 q = 1) (hb : d241832 q = 1) : d244344 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23953, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60741 q ha hb
    | true =>
      simp only [d23953, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60742 q ha hb
  have h2 (q : Pattern) (ha : d23954 q = 1) (hb : d241832 q = 1) : d244345 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23954, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23954, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23955 q = 1) (hb : d241832 q = 1) : d244346 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23955, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23955, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23957 q = 1) (hb : d241832 q = 1) : d244348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60742 q ha hb
    | true =>
      simp only [d23957, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60743 q ha hb
  have h5 (q : Pattern) (ha : d23958 q = 1) (hb : d241832 q = 1) : d244349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23959 q = 1) (hb : d241832 q = 1) : d244350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23960 q = 1) (hb : d241832 q = 1) : d244351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23960, d244351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23960, d244351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23961 q = 1) (hb : d241832 q = 1) : d244352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23961, d244352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23961, d244352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23962 q = 1) (hb : d241832 q = 1) : d244353 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23962, d244353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23962, d244353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23963 q = 1) (hb : d241832 q = 1) : d244354 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23963, d244354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23963, d244354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro60745 (p : Pattern) (ha : d23967 p = 1) (hb : d241832 p = 1) : d244358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23957 q = 1) (hb : d241832 q = 1) : d244348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60742 q ha hb
    | true =>
      simp only [d23957, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60743 q ha hb
  have h2 (q : Pattern) (ha : d23958 q = 1) (hb : d241832 q = 1) : d244349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23959 q = 1) (hb : d241832 q = 1) : d244350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23961 q = 1) (hb : d241832 q = 1) : d244352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23961, d244352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23961, d244352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23966 q = 1) (hb : d241832 q = 1) : d244357 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23966, d244357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23966, d244357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23967 q = 1) (hb : d241832 q = 1) : d244358 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23967, d244358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23967, d244358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro60746 (p : Pattern) (ha : d23973 p = 1) (hb : d241832 p = 1) : d244364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60744 q ha hb
    | true =>
      simp only [d23964, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60745 q ha hb
    | true =>
      simp only [d23968, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d241832 q = 1) : d244361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d241832 q = 1) : d244362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23972 q = 1) (hb : d241832 q = 1) : d244363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23972, d244363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23972, d244363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23973 q = 1) (hb : d241832 q = 1) : d244364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23973, d244364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23973, d244364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro60747 (p : Pattern) (ha : d23977 p = 1) (hb : d241832 p = 1) : d244368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60745 q ha hb
    | true =>
      simp only [d23968, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d241832 q = 1) : d244365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d241832 q = 1) : d244366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23976 q = 1) (hb : d241832 q = 1) : d244367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23976, d244367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23976, d244367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23977 q = 1) (hb : d241832 q = 1) : d244368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23977, d244368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23977, d244368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60748 (p : Pattern) (ha : d23983 p = 1) (hb : d241832 p = 1) : d244374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d241832 q = 1) : d244369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60746 q ha hb
    | true =>
      simp only [d23978, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60747 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d241832 q = 1) : d244370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d241832 q = 1) : d244371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d241832 q = 1) : d244372 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d241832 q = 1) : d244373 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23983 q = 1) (hb : d241832 q = 1) : d244374 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23983, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23983, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro60749 (p : Pattern) (ha : d23986 p = 1) (hb : d241832 p = 1) : d244377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60744 q ha hb
    | true =>
      simp only [d23964, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60745 q ha hb
    | true =>
      simp only [d23968, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d241832 q = 1) : d244361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d241832 q = 1) : d244362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23972 q = 1) (hb : d241832 q = 1) : d244363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23972, d244363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23972, d244363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23986 q = 1) (hb : d241832 q = 1) : d244377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23986, d244377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23986, d244377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
