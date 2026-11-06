import NetHack.Soko22Hazard87.EqIntroBlocks0077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro19500 (p : Pattern) (selected : d203508 p = 0) : d205279 p = 1 := by
  have h0 (q : Pattern) (selected : d203489 q = 0) : d205260 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203489, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19495 q selected
    | true =>
      simp only [d203489, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19496 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203490 q = 0) : d205261 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203490, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203490, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19415 q selected
  have h3 (q : Pattern) (selected : d203491 q = 0) : d205262 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203491, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203491, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203499 q = 0) : d205270 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203499, d205270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19498 q selected
    | true =>
      simp only [d203499, d205270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203500 q = 0) : d205271 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203500, d205271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203500, d205271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203501 q = 0) : d205272 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203501, d205272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203501, d205272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203502 q = 0) : d205273 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203502, d205273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203502, d205273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d203503 q = 0) : d205274 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203503, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19498 q selected
    | true =>
      simp only [d203503, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19499 q selected
  have h9 (q : Pattern) (selected : d203504 q = 0) : d205275 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203504, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203504, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19272 q selected
  have h10 (q : Pattern) (selected : d203505 q = 0) : d205276 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203505, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203505, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203506 q = 0) : d205277 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203506, d205277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203506, d205277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d203507 q = 0) : d205278 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203507, d205278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203507, d205278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d203508 q = 0) : d205279 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203508, d205279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203508, d205279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro19501 (p : Pattern) (selected : d203514 p = 0) : d205285 p = 1 := by
  have h0 (q : Pattern) (selected : d203489 q = 0) : d205260 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203489, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19495 q selected
    | true =>
      simp only [d203489, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19496 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203490 q = 0) : d205261 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203490, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203490, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19415 q selected
  have h3 (q : Pattern) (selected : d203491 q = 0) : d205262 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203491, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203491, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203492 q = 0) : d205263 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203492, d205263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203492, d205263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203493 q = 0) : d205264 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203493, d205264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203493, d205264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203503 q = 0) : d205274 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203503, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19498 q selected
    | true =>
      simp only [d203503, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19499 q selected
  have h7 (q : Pattern) (selected : d203504 q = 0) : d205275 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203504, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203504, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19272 q selected
  have h8 (q : Pattern) (selected : d203505 q = 0) : d205276 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203505, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203505, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203506 q = 0) : d205277 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203506, d205277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203506, d205277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d203507 q = 0) : d205278 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203507, d205278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203507, d205278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d203514 q = 0) : d205285 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203514, d205285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203514, d205285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19502 (p : Pattern) (selected : d1547 p = 0) : d52988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1519 q = 0) : d52960 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1531 q = 0) : d52972 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1547 q = 0) : d52988 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19503 (p : Pattern) (selected : d203523 p = 0) : d205294 p = 1 := by
  have h0 (q : Pattern) (selected : d203503 q = 0) : d205274 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203503, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19498 q selected
    | true =>
      simp only [d203503, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19499 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203504 q = 0) : d205275 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203504, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203504, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19272 q selected
  have h3 (q : Pattern) (selected : d203505 q = 0) : d205276 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203505, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203505, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203519 q = 0) : d205290 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203519, d205290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19502 q selected
    | true =>
      simp only [d203519, d205290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203520 q = 0) : d205291 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203520, d205291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203520, d205291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203521 q = 0) : d205292 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203521, d205292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203521, d205292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203522 q = 0) : d205293 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203522, d205293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203522, d205293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d203523 q = 0) : d205294 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203523, d205294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203523, d205294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro19504 (p : Pattern) (selected : d203529 p = 0) : d205300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203495 q = 0) : d205266 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203495, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19497 q selected
    | true =>
      simp only [d203495, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203496 q = 0) : d205267 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203496, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203496, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203497 q = 0) : d205268 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203497, d205268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203497, d205268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203498 q = 0) : d205269 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203498, d205269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203498, d205269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203509 q = 0) : d205280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203509, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19500 q selected
    | true =>
      simp only [d203509, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203510 q = 0) : d205281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203510, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203510, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203511 q = 0) : d205282 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203511, d205282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203511, d205282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203512 q = 0) : d205283 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203512, d205283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203512, d205283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203513 q = 0) : d205284 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203513, d205284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203513, d205284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203515 q = 0) : d205286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
    | true =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203516 q = 0) : d205287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203517 q = 0) : d205288 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203517, d205288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203517, d205288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203518 q = 0) : d205289 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203518, d205289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203518, d205289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d203524 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
    | true =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203525 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203526 q = 0) : d205297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203526, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203526, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203527 q = 0) : d205298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203527, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203527, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203528 q = 0) : d205299 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203528, d205299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203528, d205299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203529 q = 0) : d205300 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203529, d205300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203529, d205300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro19505 (p : Pattern) (selected : d203532 p = 0) : d205303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203509 q = 0) : d205280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203509, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19500 q selected
    | true =>
      simp only [d203509, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203510 q = 0) : d205281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203510, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203510, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203511 q = 0) : d205282 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203511, d205282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203511, d205282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203512 q = 0) : d205283 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203512, d205283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203512, d205283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203524 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
    | true =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203525 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203526 q = 0) : d205297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203526, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203526, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203527 q = 0) : d205298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203527, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203527, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203530 q = 0) : d205301 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203530, d205301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203530, d205301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203531 q = 0) : d205302 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203531, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203531, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203532 q = 0) : d205303 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203532, d205303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203532, d205303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19506 (p : Pattern) (selected : d203536 p = 0) : d205307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203524 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
    | true =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203525 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203526 q = 0) : d205297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203526, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203526, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203527 q = 0) : d205298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203527, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203527, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203531 q = 0) : d205302 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203531, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203531, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203536 q = 0) : d205307 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203536, d205307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203536, d205307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19507 (p : Pattern) (selected : d203543 p = 0) : d205314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203533 q = 0) : d205304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203533, d205304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19504 q selected
    | true =>
      simp only [d203533, d205304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19505 q selected
  have h2 (q : Pattern) (selected : d203534 q = 0) : d205305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203534, d205305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203534, d205305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203535 q = 0) : d205306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203535, d205306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203535, d205306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203537 q = 0) : d205308 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203537, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19505 q selected
    | true =>
      simp only [d203537, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19506 q selected
  have h5 (q : Pattern) (selected : d203538 q = 0) : d205309 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203538, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203538, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203539 q = 0) : d205310 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203539, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203539, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203540 q = 0) : d205311 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203540, d205311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203540, d205311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203541 q = 0) : d205312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203541, d205312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203541, d205312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203542 q = 0) : d205313 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203542, d205313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203542, d205313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203543 q = 0) : d205314 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203543, d205314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203543, d205314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19508 (p : Pattern) (selected : d203547 p = 0) : d205318 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203537 q = 0) : d205308 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203537, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19505 q selected
    | true =>
      simp only [d203537, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19506 q selected
  have h2 (q : Pattern) (selected : d203538 q = 0) : d205309 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203538, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203538, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203539 q = 0) : d205310 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203539, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203539, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203541 q = 0) : d205312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203541, d205312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203541, d205312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203546 q = 0) : d205317 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203546, d205317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203546, d205317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203547 q = 0) : d205318 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203547, d205318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203547, d205318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19509 (p : Pattern) (selected : d203553 p = 0) : d205324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203550 q = 0) : d205321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203551 q = 0) : d205322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203551, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203551, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203552 q = 0) : d205323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203552, d205323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203552, d205323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203553 q = 0) : d205324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203553, d205324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203553, d205324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19510 (p : Pattern) (selected : d203557 p = 0) : d205328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203554 q = 0) : d205325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203555 q = 0) : d205326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203555, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203555, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203556 q = 0) : d205327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203556, d205327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203556, d205327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203557 q = 0) : d205328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203557, d205328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203557, d205328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19511 (p : Pattern) (selected : d203563 p = 0) : d205334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203558 q = 0) : d205329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203558, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19509 q selected
    | true =>
      simp only [d203558, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19510 q selected
  have h2 (q : Pattern) (selected : d203559 q = 0) : d205330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203559, d205330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203559, d205330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203560 q = 0) : d205331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203560, d205331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203560, d205331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203561 q = 0) : d205332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203561, d205332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203561, d205332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203562 q = 0) : d205333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203562, d205333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203562, d205333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203563 q = 0) : d205334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203563, d205334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203563, d205334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19512 (p : Pattern) (selected : d203566 p = 0) : d205337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203550 q = 0) : d205321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203551 q = 0) : d205322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203551, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203551, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203552 q = 0) : d205323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203552, d205323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203552, d205323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203566 q = 0) : d205337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203566, d205337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203566, d205337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19513 (p : Pattern) (selected : d203567 p = 0) : d205338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203554 q = 0) : d205325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203555 q = 0) : d205326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203555, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203555, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203556 q = 0) : d205327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203556, d205327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203556, d205327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203567 q = 0) : d205338 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203567, d205338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203567, d205338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19514 (p : Pattern) (selected : d203573 p = 0) : d205344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203558 q = 0) : d205329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203558, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19509 q selected
    | true =>
      simp only [d203558, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19510 q selected
  have h2 (q : Pattern) (selected : d203559 q = 0) : d205330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203559, d205330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203559, d205330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203560 q = 0) : d205331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203560, d205331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203560, d205331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203561 q = 0) : d205332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203561, d205332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203561, d205332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203562 q = 0) : d205333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203562, d205333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203562, d205333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203568 q = 0) : d205339 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203568, d205339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19512 q selected
    | true =>
      simp only [d203568, d205339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19513 q selected
  have h7 (q : Pattern) (selected : d203569 q = 0) : d205340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203569, d205340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203569, d205340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203570 q = 0) : d205341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203570, d205341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203570, d205341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203571 q = 0) : d205342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203571, d205342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203571, d205342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203572 q = 0) : d205343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203572, d205343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203572, d205343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203573 q = 0) : d205344 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203573, d205344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203573, d205344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19515 (p : Pattern) (selected : d203578 p = 0) : d205349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203550 q = 0) : d205321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203551 q = 0) : d205322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203551, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203551, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203577 q = 0) : d205348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203577, d205348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203577, d205348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203578 q = 0) : d205349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203578, d205349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203578, d205349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19516 (p : Pattern) (selected : d203580 p = 0) : d205351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203554 q = 0) : d205325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203555 q = 0) : d205326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203555, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203555, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203579 q = 0) : d205350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203579, d205350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203579, d205350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203580 q = 0) : d205351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203580, d205351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203580, d205351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19517 (p : Pattern) (selected : d203587 p = 0) : d205358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203550 q = 0) : d205321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203585 q = 0) : d205356 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203585, d205356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203585, d205356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203586 q = 0) : d205357 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203586, d205357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203586, d205357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203587 q = 0) : d205358 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203587, d205358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203587, d205358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19518 (p : Pattern) (selected : d203590 p = 0) : d205361 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203554 q = 0) : d205325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203588 q = 0) : d205359 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203588, d205359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203588, d205359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203589 q = 0) : d205360 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203589, d205360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203589, d205360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203590 q = 0) : d205361 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203590, d205361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203590, d205361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19519 (p : Pattern) (selected : d203596 p = 0) : d205367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203163 q = 0) : d205054 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203163, d205054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19435 q selected
    | true =>
      simp only [d203163, d205054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203164 q = 0) : d205055 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203164, d205055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203164, d205055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203594 q = 0) : d205365 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203594, d205365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203594, d205365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203595 q = 0) : d205366 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203595, d205366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203595, d205366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203596 q = 0) : d205367 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203596, d205367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203596, d205367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro19520 (p : Pattern) (selected : d203602 p = 0) : d205373 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203163 q = 0) : d205054 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203163, d205054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19435 q selected
    | true =>
      simp only [d203163, d205054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203164 q = 0) : d205055 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203164, d205055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203164, d205055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203594 q = 0) : d205365 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203594, d205365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203594, d205365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203595 q = 0) : d205366 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203595, d205366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203595, d205366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203489 q = 0) : d205260 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203489, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19495 q selected
    | true =>
      simp only [d203489, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19496 q selected
  have h6 (q : Pattern) (selected : d203490 q = 0) : d205261 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203490, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203490, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19415 q selected
  have h7 (q : Pattern) (selected : d203491 q = 0) : d205262 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203491, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203491, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203492 q = 0) : d205263 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203492, d205263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203492, d205263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203493 q = 0) : d205264 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203493, d205264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203493, d205264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d203602 q = 0) : d205373 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203602, d205373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203602, d205373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro19521 (p : Pattern) (selected : d203608 p = 0) : d205379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203597 q = 0) : d205368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203597, d205368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19519 q selected
    | true =>
      simp only [d203597, d205368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203598 q = 0) : d205369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203598, d205369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203598, d205369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203599 q = 0) : d205370 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203599, d205370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203599, d205370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203600 q = 0) : d205371 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203600, d205371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203600, d205371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203495 q = 0) : d205266 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203495, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19497 q selected
    | true =>
      simp only [d203495, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203496 q = 0) : d205267 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203496, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203496, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203497 q = 0) : d205268 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203497, d205268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203497, d205268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203498 q = 0) : d205269 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203498, d205269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203498, d205269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203601 q = 0) : d205372 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203601, d205372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203601, d205372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203603 q = 0) : d205374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203603, d205374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19520 q selected
    | true =>
      simp only [d203603, d205374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203604 q = 0) : d205375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203604, d205375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203604, d205375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203605 q = 0) : d205376 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203605, d205376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203605, d205376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203606 q = 0) : d205377 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203606, d205377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203606, d205377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d203515 q = 0) : d205286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
    | true =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203516 q = 0) : d205287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203517 q = 0) : d205288 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203517, d205288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203517, d205288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203518 q = 0) : d205289 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203518, d205289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203518, d205289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203607 q = 0) : d205378 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203607, d205378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203607, d205378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203608 q = 0) : d205379 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203608, d205379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203608, d205379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro19522 (p : Pattern) (selected : d203612 p = 0) : d205383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203515 q = 0) : d205286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
    | true =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203516 q = 0) : d205287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203517 q = 0) : d205288 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203517, d205288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203517, d205288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203518 q = 0) : d205289 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203518, d205289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203518, d205289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203524 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
    | true =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203525 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203526 q = 0) : d205297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203526, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203526, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203527 q = 0) : d205298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203527, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203527, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203528 q = 0) : d205299 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203528, d205299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203528, d205299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203531 q = 0) : d205302 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203531, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203531, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203612 q = 0) : d205383 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203612, d205383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203612, d205383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19523 (p : Pattern) (selected : d203618 p = 0) : d205389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203609 q = 0) : d205380 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203609, d205380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19521 q selected
    | true =>
      simp only [d203609, d205380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19504 q selected
  have h2 (q : Pattern) (selected : d203610 q = 0) : d205381 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203610, d205381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203610, d205381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203611 q = 0) : d205382 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203611, d205382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203611, d205382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203613 q = 0) : d205384 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203613, d205384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19504 q selected
    | true =>
      simp only [d203613, d205384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19522 q selected
  have h5 (q : Pattern) (selected : d203614 q = 0) : d205385 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203614, d205385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203614, d205385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203615 q = 0) : d205386 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203615, d205386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203615, d205386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203616 q = 0) : d205387 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203616, d205387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203616, d205387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203533 q = 0) : d205304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203533, d205304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19504 q selected
    | true =>
      simp only [d203533, d205304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19505 q selected
  have h9 (q : Pattern) (selected : d203534 q = 0) : d205305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203534, d205305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203534, d205305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203535 q = 0) : d205306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203535, d205306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203535, d205306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203537 q = 0) : d205308 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203537, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19505 q selected
    | true =>
      simp only [d203537, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19506 q selected
  have h12 (q : Pattern) (selected : d203538 q = 0) : d205309 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203538, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203538, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203539 q = 0) : d205310 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203539, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203539, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203540 q = 0) : d205311 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203540, d205311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203540, d205311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d203617 q = 0) : d205388 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203617, d205388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203617, d205388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d203618 q = 0) : d205389 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203618, d205389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203618, d205389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro19524 (p : Pattern) (selected : d203624 p = 0) : d205395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203619 q = 0) : d205390 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203619, d205390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19523 q selected
    | true =>
      simp only [d203619, d205390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203620 q = 0) : d205391 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203620, d205391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203620, d205391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203621 q = 0) : d205392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203621, d205392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203621, d205392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203622 q = 0) : d205393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203622, d205393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203622, d205393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203623 q = 0) : d205394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203623, d205394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203623, d205394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203624 q = 0) : d205395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203624, d205395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203624, d205395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19525 (p : Pattern) (selected : d1229 p = 0) : d52497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 0) : d52108 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d853 q = 0) : d52275 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d853, d52275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d853, d52275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1229 q = 0) : d52497 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1229, d52497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1229, d52497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro19526 (p : Pattern) (selected : d1241 p = 0) : d52503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 0) : d52108 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d853 q = 0) : d52275 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d853, d52275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d853, d52275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1240 q = 0) : d52502 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1240, d52502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1240, d52502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1241 q = 0) : d52503 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1241, d52503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1241, d52503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19527 (p : Pattern) (selected : d1689 p = 0) : d52962 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 0) : d52108 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d853 q = 0) : d52275 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d853, d52275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d853, d52275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1687 q = 0) : d52960 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1687, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1687, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1688 q = 0) : d52961 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1688, d52961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1688, d52961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1689 q = 0) : d52962 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1689, d52962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1689, d52962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19528 (p : Pattern) (selected : d1693 p = 0) : d52966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d159 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1233 q = 0) : d52665 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1692 q = 0) : d52965 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1692, d52965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1692, d52965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1693 q = 0) : d52966 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1693, d52966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1693, d52966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro19529 (p : Pattern) (selected : d203637 p = 0) : d205265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203626 q = 0) : d205054 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203626, d205054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19525 q selected
    | true =>
      simp only [d203626, d205054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203627 q = 0) : d205055 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203627, d205055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203627, d205055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203628 q = 0) : d205056 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203628, d205056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19526 q selected
    | true =>
      simp only [d203628, d205056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203629 q = 0) : d205057 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203629, d205057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203629, d205057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203630 q = 0) : d205058 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203630, d205058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203630, d205058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203631 q = 0) : d205059 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203631, d205059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203631, d205059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203632 q = 0) : d205260 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203632, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19527 q selected
    | true =>
      simp only [d203632, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19528 q selected
  have h8 (q : Pattern) (selected : d203633 q = 0) : d205261 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203633, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203633, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19445 q selected
  have h9 (q : Pattern) (selected : d203634 q = 0) : d205262 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203634, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203634, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203635 q = 0) : d205263 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203635, d205263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203635, d205263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203636 q = 0) : d205264 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203636, d205264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203636, d205264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203637 q = 0) : d205265 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203637, d205265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203637, d205265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro19530 (p : Pattern) (selected : d1703 p = 0) : d52973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 0) : d52108 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1687 q = 0) : d52960 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1687, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1687, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1688 q = 0) : d52961 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1688, d52961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1688, d52961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1702 q = 0) : d52972 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1702, d52972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1702, d52972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1703 q = 0) : d52973 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1703, d52973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1703, d52973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19531 (p : Pattern) (selected : d1712 p = 0) : d52982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1687 q = 0) : d52960 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1687, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1687, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d159 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d160 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d160, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1711 q = 0) : d52981 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1711, d52981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1711, d52981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1712 q = 0) : d52982 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1712, d52982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1712, d52982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro19532 (p : Pattern) (selected : d203651 p = 0) : d205279 p = 1 := by
  have h0 (q : Pattern) (selected : d203632 q = 0) : d205260 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203632, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19527 q selected
    | true =>
      simp only [d203632, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19528 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203633 q = 0) : d205261 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203633, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203633, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19445 q selected
  have h3 (q : Pattern) (selected : d203634 q = 0) : d205262 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203634, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203634, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203642 q = 0) : d205270 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203642, d205270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19530 q selected
    | true =>
      simp only [d203642, d205270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203643 q = 0) : d205271 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203643, d205271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203643, d205271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203644 q = 0) : d205272 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203644, d205272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203644, d205272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203645 q = 0) : d205273 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203645, d205273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203645, d205273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d203646 q = 0) : d205274 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203646, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19530 q selected
    | true =>
      simp only [d203646, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19531 q selected
  have h9 (q : Pattern) (selected : d203647 q = 0) : d205275 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203647, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203647, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19295 q selected
  have h10 (q : Pattern) (selected : d203648 q = 0) : d205276 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203648, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203648, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203649 q = 0) : d205277 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203649, d205277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203649, d205277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d203650 q = 0) : d205278 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203650, d205278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203650, d205278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d203651 q = 0) : d205279 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203651, d205279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203651, d205279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro19533 (p : Pattern) (selected : d203657 p = 0) : d205285 p = 1 := by
  have h0 (q : Pattern) (selected : d203632 q = 0) : d205260 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203632, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19527 q selected
    | true =>
      simp only [d203632, d205260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19528 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203633 q = 0) : d205261 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203633, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203633, d205261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19445 q selected
  have h3 (q : Pattern) (selected : d203634 q = 0) : d205262 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203634, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203634, d205262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203635 q = 0) : d205263 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203635, d205263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203635, d205263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203636 q = 0) : d205264 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203636, d205264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203636, d205264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203646 q = 0) : d205274 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203646, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19530 q selected
    | true =>
      simp only [d203646, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19531 q selected
  have h7 (q : Pattern) (selected : d203647 q = 0) : d205275 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203647, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203647, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19295 q selected
  have h8 (q : Pattern) (selected : d203648 q = 0) : d205276 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203648, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203648, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203649 q = 0) : d205277 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203649, d205277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203649, d205277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d203650 q = 0) : d205278 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203650, d205278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203650, d205278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d203657 q = 0) : d205285 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203657, d205285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203657, d205285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19534 (p : Pattern) (selected : d1718 p = 0) : d52988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1687 q = 0) : d52960 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1687, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1687, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1702 q = 0) : d52972 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1702, d52972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1702, d52972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1718 q = 0) : d52988 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1718, d52988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1718, d52988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19535 (p : Pattern) (selected : d203666 p = 0) : d205294 p = 1 := by
  have h0 (q : Pattern) (selected : d203646 q = 0) : d205274 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203646, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19530 q selected
    | true =>
      simp only [d203646, d205274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19531 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203647 q = 0) : d205275 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203647, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203647, d205275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19295 q selected
  have h3 (q : Pattern) (selected : d203648 q = 0) : d205276 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203648, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203648, d205276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203662 q = 0) : d205290 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203662, d205290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19534 q selected
    | true =>
      simp only [d203662, d205290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203663 q = 0) : d205291 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203663, d205291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203663, d205291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203664 q = 0) : d205292 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203664, d205292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203664, d205292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203665 q = 0) : d205293 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203665, d205293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203665, d205293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d203666 q = 0) : d205294 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203666, d205294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203666, d205294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro19536 (p : Pattern) (selected : d203672 p = 0) : d205300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203638 q = 0) : d205266 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203638, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19529 q selected
    | true =>
      simp only [d203638, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203639 q = 0) : d205267 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203639, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203639, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203640 q = 0) : d205268 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203640, d205268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203640, d205268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203641 q = 0) : d205269 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203641, d205269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203641, d205269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203652 q = 0) : d205280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203652, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19532 q selected
    | true =>
      simp only [d203652, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203653 q = 0) : d205281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203653, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203653, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203654 q = 0) : d205282 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203654, d205282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203654, d205282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203655 q = 0) : d205283 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203655, d205283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203655, d205283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203656 q = 0) : d205284 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203656, d205284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203656, d205284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203658 q = 0) : d205286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203658, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19533 q selected
    | true =>
      simp only [d203658, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203659 q = 0) : d205287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203659, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203659, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203660 q = 0) : d205288 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203660, d205288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203660, d205288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203661 q = 0) : d205289 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203661, d205289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203661, d205289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d203667 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
    | true =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203668 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203669 q = 0) : d205297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203669, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203669, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203670 q = 0) : d205298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203670, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203670, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203671 q = 0) : d205299 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203671, d205299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203671, d205299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203672 q = 0) : d205300 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203672, d205300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203672, d205300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro19537 (p : Pattern) (selected : d203675 p = 0) : d205303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203652 q = 0) : d205280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203652, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19532 q selected
    | true =>
      simp only [d203652, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203653 q = 0) : d205281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203653, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203653, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203654 q = 0) : d205282 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203654, d205282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203654, d205282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203655 q = 0) : d205283 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203655, d205283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203655, d205283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203667 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
    | true =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203668 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203669 q = 0) : d205297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203669, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203669, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203670 q = 0) : d205298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203670, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203670, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203673 q = 0) : d205301 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203673, d205301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203673, d205301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203674 q = 0) : d205302 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203674, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203674, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203675 q = 0) : d205303 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203675, d205303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203675, d205303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19538 (p : Pattern) (selected : d203679 p = 0) : d205307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203667 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
    | true =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203668 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203669 q = 0) : d205297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203669, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203669, d205297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203670 q = 0) : d205298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203670, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203670, d205298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203674 q = 0) : d205302 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203674, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203674, d205302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203679 q = 0) : d205307 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203679, d205307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203679, d205307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19539 (p : Pattern) (selected : d203686 p = 0) : d205314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203676 q = 0) : d205304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203676, d205304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19536 q selected
    | true =>
      simp only [d203676, d205304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19537 q selected
  have h2 (q : Pattern) (selected : d203677 q = 0) : d205305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203677, d205305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203677, d205305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203678 q = 0) : d205306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203678, d205306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203678, d205306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203680 q = 0) : d205308 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203680, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19537 q selected
    | true =>
      simp only [d203680, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19538 q selected
  have h5 (q : Pattern) (selected : d203681 q = 0) : d205309 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203681, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203681, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203682 q = 0) : d205310 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203682, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203682, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203683 q = 0) : d205311 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203683, d205311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203683, d205311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203684 q = 0) : d205312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203684, d205312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203684, d205312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203685 q = 0) : d205313 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203685, d205313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203685, d205313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203686 q = 0) : d205314 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203686, d205314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203686, d205314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19540 (p : Pattern) (selected : d203690 p = 0) : d205318 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203680 q = 0) : d205308 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203680, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19537 q selected
    | true =>
      simp only [d203680, d205308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19538 q selected
  have h2 (q : Pattern) (selected : d203681 q = 0) : d205309 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203681, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203681, d205309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203682 q = 0) : d205310 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203682, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203682, d205310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203684 q = 0) : d205312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203684, d205312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203684, d205312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203689 q = 0) : d205317 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203689, d205317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203689, d205317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203690 q = 0) : d205318 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203690, d205318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203690, d205318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19541 (p : Pattern) (selected : d203696 p = 0) : d205324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203687 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203687, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19539 q selected
    | true =>
      simp only [d203687, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203688 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203688, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203688, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203691 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203691, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19540 q selected
    | true =>
      simp only [d203691, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203692 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203692, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203692, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203693 q = 0) : d205321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203693, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203693, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203694 q = 0) : d205322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203694, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203694, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203695 q = 0) : d205323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203695, d205323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203695, d205323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203696 q = 0) : d205324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203696, d205324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203696, d205324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19542 (p : Pattern) (selected : d203700 p = 0) : d205328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203691 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203691, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19540 q selected
    | true =>
      simp only [d203691, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203692 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203692, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203692, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203697 q = 0) : d205325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203697, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203697, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203698 q = 0) : d205326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203698, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203698, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203699 q = 0) : d205327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203699, d205327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203699, d205327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203700 q = 0) : d205328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203700, d205328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203700, d205328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19543 (p : Pattern) (selected : d203706 p = 0) : d205401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203703 q = 0) : d205398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203703, d205398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203703, d205398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203704 q = 0) : d205399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203704, d205399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203704, d205399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203705 q = 0) : d205400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203705, d205400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203705, d205400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203706 q = 0) : d205401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203706, d205401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203706, d205401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19544 (p : Pattern) (selected : d203712 p = 0) : d205407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203581 q = 0) : d205352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203581, d205352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19515 q selected
    | true =>
      simp only [d203581, d205352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19516 q selected
  have h2 (q : Pattern) (selected : d203582 q = 0) : d205353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203582, d205353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203582, d205353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203583 q = 0) : d205354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203583, d205354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203583, d205354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203584 q = 0) : d205355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203584, d205355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203584, d205355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203591 q = 0) : d205362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203591, d205362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19517 q selected
    | true =>
      simp only [d203591, d205362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19518 q selected
  have h6 (q : Pattern) (selected : d203592 q = 0) : d205363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203592, d205363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203592, d205363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203593 q = 0) : d205364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203593, d205364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203593, d205364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203625 q = 0) : d205396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203625, d205396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19524 q selected
    | true =>
      simp only [d203625, d205396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19509 q selected
  have h9 (q : Pattern) (selected : d203701 q = 0) : d205329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203701, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19541 q selected
    | true =>
      simp only [d203701, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19542 q selected
  have h10 (q : Pattern) (selected : d203702 q = 0) : d205397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203702, d205397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203702, d205397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203707 q = 0) : d205402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203707, d205402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19543 q selected
    | true =>
      simp only [d203707, d205402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203708 q = 0) : d205403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203708, d205403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203708, d205403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203709 q = 0) : d205404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203709, d205404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203709, d205404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203710 q = 0) : d205405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203710, d205405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203710, d205405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d203711 q = 0) : d205406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203711, d205406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203711, d205406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d203712 q = 0) : d205407 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203712, d205407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203712, d205407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro19545 (p : Pattern) (selected : d203713 p = 0) : d205408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203550 q = 0) : d205321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203551 q = 0) : d205322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203551, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203551, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203577 q = 0) : d205348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203577, d205348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203577, d205348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203713 q = 0) : d205408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203713, d205408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203713, d205408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19546 (p : Pattern) (selected : d203714 p = 0) : d205409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203554 q = 0) : d205325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203555 q = 0) : d205326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203555, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203555, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203579 q = 0) : d205350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203579, d205350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203579, d205350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203714 q = 0) : d205409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203714, d205409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203714, d205409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19547 (p : Pattern) (selected : d203719 p = 0) : d205414 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203550 q = 0) : d205321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203550, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203585 q = 0) : d205356 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203585, d205356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203585, d205356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203586 q = 0) : d205357 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203586, d205357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203586, d205357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203719 q = 0) : d205414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203719, d205414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203719, d205414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19548 (p : Pattern) (selected : d203720 p = 0) : d205415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203548 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19508 q selected
    | true =>
      simp only [d203548, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203549 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203549, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203554 q = 0) : d205325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203554, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203588 q = 0) : d205359 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203588, d205359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203588, d205359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203589 q = 0) : d205360 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203589, d205360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203589, d205360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203720 q = 0) : d205415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203720, d205415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203720, d205415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19549 (p : Pattern) (selected : d203724 p = 0) : d205419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203619 q = 0) : d205390 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203619, d205390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19523 q selected
    | true =>
      simp only [d203619, d205390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203620 q = 0) : d205391 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203620, d205391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203620, d205391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203621 q = 0) : d205392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203621, d205392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203621, d205392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203622 q = 0) : d205393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203622, d205393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203622, d205393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203623 q = 0) : d205394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203623, d205394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203623, d205394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203724 q = 0) : d205419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203724, d205419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203724, d205419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19550 (p : Pattern) (selected : d203726 p = 0) : d205337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203687 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203687, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19539 q selected
    | true =>
      simp only [d203687, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203688 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203688, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203688, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203691 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203691, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19540 q selected
    | true =>
      simp only [d203691, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203692 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203692, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203692, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203693 q = 0) : d205321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203693, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203693, d205321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203694 q = 0) : d205322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203694, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203694, d205322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203695 q = 0) : d205323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203695, d205323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203695, d205323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203726 q = 0) : d205337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203726, d205337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203726, d205337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19551 (p : Pattern) (selected : d203727 p = 0) : d205338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203691 q = 0) : d205319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203691, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19540 q selected
    | true =>
      simp only [d203691, d205319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203692 q = 0) : d205320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203692, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203692, d205320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203697 q = 0) : d205325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203697, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203697, d205325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203698 q = 0) : d205326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203698, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203698, d205326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203699 q = 0) : d205327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203699, d205327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203699, d205327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203727 q = 0) : d205338 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203727, d205338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203727, d205338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19552 (p : Pattern) (selected : d203730 p = 0) : d205422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203544 q = 0) : d205315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19507 q selected
    | true =>
      simp only [d203544, d205315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203545 q = 0) : d205316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203545, d205316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203703 q = 0) : d205398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203703, d205398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203703, d205398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203704 q = 0) : d205399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203704, d205399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203704, d205399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203705 q = 0) : d205400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203705, d205400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203705, d205400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203730 q = 0) : d205422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203730, d205422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203730, d205422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19553 (p : Pattern) (selected : d203736 p = 0) : d205428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203581 q = 0) : d205352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203581, d205352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19515 q selected
    | true =>
      simp only [d203581, d205352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19516 q selected
  have h2 (q : Pattern) (selected : d203582 q = 0) : d205353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203582, d205353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203582, d205353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203583 q = 0) : d205354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203583, d205354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203583, d205354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203584 q = 0) : d205355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203584, d205355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203584, d205355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203591 q = 0) : d205362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203591, d205362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19517 q selected
    | true =>
      simp only [d203591, d205362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19518 q selected
  have h6 (q : Pattern) (selected : d203592 q = 0) : d205363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203592, d205363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203592, d205363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203593 q = 0) : d205364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203593, d205364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203593, d205364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203625 q = 0) : d205396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203625, d205396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19524 q selected
    | true =>
      simp only [d203625, d205396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19509 q selected
  have h9 (q : Pattern) (selected : d203701 q = 0) : d205329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203701, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19541 q selected
    | true =>
      simp only [d203701, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19542 q selected
  have h10 (q : Pattern) (selected : d203702 q = 0) : d205397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203702, d205397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203702, d205397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203707 q = 0) : d205402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203707, d205402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19543 q selected
    | true =>
      simp only [d203707, d205402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203708 q = 0) : d205403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203708, d205403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203708, d205403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203709 q = 0) : d205404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203709, d205404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203709, d205404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203710 q = 0) : d205405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203710, d205405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203710, d205405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d203711 q = 0) : d205406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203711, d205406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203711, d205406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d203715 q = 0) : d205410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203715, d205410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19545 q selected
    | true =>
      simp only [d203715, d205410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19546 q selected
  have h17 (q : Pattern) (selected : d203716 q = 0) : d205411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203716, d205411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203716, d205411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d203717 q = 0) : d205412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203717, d205412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d203717, d205412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d203718 q = 0) : d205413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203718, d205413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203718, d205413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d203721 q = 0) : d205416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203721, d205416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19547 q selected
    | true =>
      simp only [d203721, d205416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19548 q selected
  have h21 (q : Pattern) (selected : d203722 q = 0) : d205417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203722, d205417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203722, d205417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d203723 q = 0) : d205418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203723, d205418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d203723, d205418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d203725 q = 0) : d205420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203725, d205420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19549 q selected
    | true =>
      simp only [d203725, d205420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19512 q selected
  have h24 (q : Pattern) (selected : d203728 q = 0) : d205339 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203728, d205339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19550 q selected
    | true =>
      simp only [d203728, d205339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19551 q selected
  have h25 (q : Pattern) (selected : d203729 q = 0) : d205421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203729, d205421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d203729, d205421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d203731 q = 0) : d205423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203731, d205423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19552 q selected
    | true =>
      simp only [d203731, d205423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d203732 q = 0) : d205424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203732, d205424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d203732, d205424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d203733 q = 0) : d205425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203733, d205425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d203733, d205425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d203734 q = 0) : d205426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203734, d205426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d203734, d205426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d203735 q = 0) : d205427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203735, d205427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d203735, d205427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d203736 q = 0) : d205428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203736, d205428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203736, d205428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro19554 (p : Pattern) (selected : d203743 p = 0) : d205435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203558 q = 0) : d205329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203558, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19509 q selected
    | true =>
      simp only [d203558, d205329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19510 q selected
  have h2 (q : Pattern) (selected : d203559 q = 0) : d205330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203559, d205330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203559, d205330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203560 q = 0) : d205331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203560, d205331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203560, d205331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203561 q = 0) : d205332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203561, d205332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203561, d205332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203562 q = 0) : d205333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203562, d205333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203562, d205333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203738 q = 0) : d205430 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203738, d205430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19510 q selected
    | true =>
      simp only [d203738, d205430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203739 q = 0) : d205431 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203739, d205431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203739, d205431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203740 q = 0) : d205432 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203740, d205432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203740, d205432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203741 q = 0) : d205433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203741, d205433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203741, d205433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203742 q = 0) : d205434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203742, d205434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203742, d205434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203743 q = 0) : d205435 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203743, d205435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203743, d205435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19555 (p : Pattern) (selected : d203749 p = 0) : d205441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203738 q = 0) : d205430 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203738, d205430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19510 q selected
    | true =>
      simp only [d203738, d205430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203739 q = 0) : d205431 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203739, d205431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203739, d205431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203740 q = 0) : d205432 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203740, d205432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203740, d205432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203741 q = 0) : d205433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203741, d205433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203741, d205433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203742 q = 0) : d205434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203742, d205434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203742, d205434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203744 q = 0) : d205436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203744, d205436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19513 q selected
    | true =>
      simp only [d203744, d205436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203745 q = 0) : d205437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203745, d205437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203745, d205437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203746 q = 0) : d205438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203746, d205438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203746, d205438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203747 q = 0) : d205439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203747, d205439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203747, d205439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203748 q = 0) : d205440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203748, d205440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203748, d205440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203749 q = 0) : d205441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203749, d205441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203749, d205441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19556 (p : Pattern) (selected : d203756 p = 0) : d205448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203725 q = 0) : d205420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203725, d205420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19549 q selected
    | true =>
      simp only [d203725, d205420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19512 q selected
  have h2 (q : Pattern) (selected : d203728 q = 0) : d205339 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203728, d205339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19550 q selected
    | true =>
      simp only [d203728, d205339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19551 q selected
  have h3 (q : Pattern) (selected : d203729 q = 0) : d205421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203729, d205421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203729, d205421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203731 q = 0) : d205423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203731, d205423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19552 q selected
    | true =>
      simp only [d203731, d205423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203732 q = 0) : d205424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203732, d205424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203732, d205424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203733 q = 0) : d205425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203733, d205425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203733, d205425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203754 q = 0) : d205446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203754, d205446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203754, d205446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203755 q = 0) : d205447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203755, d205447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203755, d205447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203756 q = 0) : d205448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203756, d205448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203756, d205448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19557 (p : Pattern) (selected : d203758 p = 0) : d205450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203744 q = 0) : d205436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203744, d205436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19513 q selected
    | true =>
      simp only [d203744, d205436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203745 q = 0) : d205437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203745, d205437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203745, d205437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203746 q = 0) : d205438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203746, d205438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203746, d205438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203747 q = 0) : d205439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203747, d205439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203747, d205439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203748 q = 0) : d205440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203748, d205440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203748, d205440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203758 q = 0) : d205450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203758, d205450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203758, d205450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19558 (p : Pattern) (selected : d203782 p = 0) : d205474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203764 q = 0) : d205456 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203764, d205456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203764, d205456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19519 q selected
  have h2 (q : Pattern) (selected : d203597 q = 0) : d205368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203597, d205368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19519 q selected
    | true =>
      simp only [d203597, d205368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203765 q = 0) : d205457 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203765, d205457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203765, d205457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203598 q = 0) : d205369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203598, d205369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203598, d205369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203766 q = 0) : d205458 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203766, d205458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203766, d205458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203767 q = 0) : d205459 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203767, d205459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203767, d205459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203768 q = 0) : d205460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203768, d205460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203768, d205460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19497 q selected
  have h8 (q : Pattern) (selected : d203495 q = 0) : d205266 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203495, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19497 q selected
    | true =>
      simp only [d203495, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203769 q = 0) : d205461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203769, d205461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203769, d205461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203496 q = 0) : d205267 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203496, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203496, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203770 q = 0) : d205462 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203770, d205462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203770, d205462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203771 q = 0) : d205463 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203771, d205463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203771, d205463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203772 q = 0) : d205464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203772, d205464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203772, d205464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203773 q = 0) : d205465 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203773, d205465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203773, d205465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19520 q selected
  have h15 (q : Pattern) (selected : d203603 q = 0) : d205374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203603, d205374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19520 q selected
    | true =>
      simp only [d203603, d205374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203774 q = 0) : d205466 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203774, d205466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203774, d205466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203604 q = 0) : d205375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203604, d205375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203604, d205375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203775 q = 0) : d205467 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203775, d205467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203775, d205467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203776 q = 0) : d205468 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203776, d205468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d203776, d205468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d203777 q = 0) : d205469 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203777, d205469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203777, d205469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
  have h21 (q : Pattern) (selected : d203515 q = 0) : d205286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
    | true =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d203778 q = 0) : d205470 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203778, d205470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d203778, d205470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d203516 q = 0) : d205287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d203779 q = 0) : d205471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203779, d205471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d203779, d205471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d203780 q = 0) : d205472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203780, d205472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d203780, d205472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d203781 q = 0) : d205473 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203781, d205473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d203781, d205473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d203782 q = 0) : d205474 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203782, d205474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203782, d205474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro19559 (p : Pattern) (selected : d203793 p = 0) : d205485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203768 q = 0) : d205460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203768, d205460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203768, d205460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19497 q selected
  have h2 (q : Pattern) (selected : d203495 q = 0) : d205266 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203495, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19497 q selected
    | true =>
      simp only [d203495, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203769 q = 0) : d205461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203769, d205461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203769, d205461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203496 q = 0) : d205267 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203496, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203496, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203770 q = 0) : d205462 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203770, d205462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203770, d205462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203771 q = 0) : d205463 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203771, d205463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203771, d205463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203783 q = 0) : d205475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203783, d205475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203783, d205475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19500 q selected
  have h8 (q : Pattern) (selected : d203509 q = 0) : d205280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203509, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19500 q selected
    | true =>
      simp only [d203509, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203784 q = 0) : d205476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203784, d205476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203784, d205476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203510 q = 0) : d205281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203510, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203510, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203785 q = 0) : d205477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203785, d205477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203785, d205477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203786 q = 0) : d205478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203786, d205478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203786, d205478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203787 q = 0) : d205479 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203787, d205479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203787, d205479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203777 q = 0) : d205469 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203777, d205469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203777, d205469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
  have h15 (q : Pattern) (selected : d203515 q = 0) : d205286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
    | true =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203778 q = 0) : d205470 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203778, d205470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203778, d205470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203516 q = 0) : d205287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203779 q = 0) : d205471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203779, d205471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203779, d205471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203780 q = 0) : d205472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203780, d205472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d203780, d205472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d203788 q = 0) : d205480 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203788, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203788, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
  have h21 (q : Pattern) (selected : d203524 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
    | true =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d203789 q = 0) : d205481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203789, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d203789, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d203525 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d203790 q = 0) : d205482 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203790, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d203790, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d203791 q = 0) : d205483 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203791, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d203791, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d203792 q = 0) : d205484 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203792, d205484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d203792, d205484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d203793 q = 0) : d205485 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203793, d205485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203793, d205485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro19560 (p : Pattern) (selected : d203798 p = 0) : d205490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203777 q = 0) : d205469 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203777, d205469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203777, d205469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
  have h2 (q : Pattern) (selected : d203515 q = 0) : d205286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19501 q selected
    | true =>
      simp only [d203515, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203778 q = 0) : d205470 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203778, d205470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203778, d205470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203516 q = 0) : d205287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203516, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203779 q = 0) : d205471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203779, d205471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203779, d205471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203780 q = 0) : d205472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203780, d205472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203780, d205472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203788 q = 0) : d205480 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203788, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203788, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
  have h8 (q : Pattern) (selected : d203524 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
    | true =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203789 q = 0) : d205481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203789, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203789, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203525 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203790 q = 0) : d205482 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203790, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203790, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203791 q = 0) : d205483 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203791, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203791, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203792 q = 0) : d205484 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203792, d205484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203792, d205484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203797 q = 0) : d205489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203797, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203797, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203798 q = 0) : d205490 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203798, d205490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203798, d205490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19561 (p : Pattern) (selected : d203804 p = 0) : d205496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203783 q = 0) : d205475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203783, d205475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203783, d205475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19500 q selected
  have h2 (q : Pattern) (selected : d203509 q = 0) : d205280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203509, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19500 q selected
    | true =>
      simp only [d203509, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203784 q = 0) : d205476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203784, d205476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203784, d205476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203510 q = 0) : d205281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203510, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203510, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203785 q = 0) : d205477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203785, d205477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203785, d205477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203786 q = 0) : d205478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203786, d205478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203786, d205478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203788 q = 0) : d205480 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203788, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203788, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
  have h8 (q : Pattern) (selected : d203524 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
    | true =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203789 q = 0) : d205481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203789, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203789, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203525 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203790 q = 0) : d205482 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203790, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203790, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203791 q = 0) : d205483 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203791, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203791, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203803 q = 0) : d205495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203803, d205495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203803, d205495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203797 q = 0) : d205489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203797, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203797, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203804 q = 0) : d205496 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203804, d205496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203804, d205496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19562 (p : Pattern) (selected : d203808 p = 0) : d205500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203788 q = 0) : d205480 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203788, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203788, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
  have h2 (q : Pattern) (selected : d203524 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19503 q selected
    | true =>
      simp only [d203524, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203789 q = 0) : d205481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203789, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203789, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203525 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203525, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203790 q = 0) : d205482 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203790, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203790, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203791 q = 0) : d205483 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203791, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203791, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203797 q = 0) : d205489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203797, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203797, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203808 q = 0) : d205500 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203808, d205500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203808, d205500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19563 (p : Pattern) (selected : d203814 p = 0) : d205506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203794 q = 0) : d205486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203794, d205486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19558 q selected
    | true =>
      simp only [d203794, d205486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19559 q selected
  have h2 (q : Pattern) (selected : d203795 q = 0) : d205487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203795, d205487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203795, d205487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203796 q = 0) : d205488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203796, d205488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203796, d205488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203799 q = 0) : d205491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203799, d205491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19559 q selected
    | true =>
      simp only [d203799, d205491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19560 q selected
  have h5 (q : Pattern) (selected : d203800 q = 0) : d205492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203800, d205492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203800, d205492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203801 q = 0) : d205493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203801, d205493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203801, d205493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203802 q = 0) : d205494 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203802, d205494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203802, d205494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203805 q = 0) : d205497 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203805, d205497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19559 q selected
    | true =>
      simp only [d203805, d205497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19561 q selected
  have h9 (q : Pattern) (selected : d203806 q = 0) : d205498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203806, d205498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203806, d205498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203807 q = 0) : d205499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203807, d205499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203807, d205499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203809 q = 0) : d205501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203809, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19561 q selected
    | true =>
      simp only [d203809, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19562 q selected
  have h12 (q : Pattern) (selected : d203810 q = 0) : d205502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203810, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203810, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203811 q = 0) : d205503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203811, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203811, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203812 q = 0) : d205504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203812, d205504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203812, d205504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d203813 q = 0) : d205505 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203813, d205505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203813, d205505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d203814 q = 0) : d205506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203814, d205506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203814, d205506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro19564 (p : Pattern) (selected : d203819 p = 0) : d205511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203805 q = 0) : d205497 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203805, d205497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19559 q selected
    | true =>
      simp only [d203805, d205497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19561 q selected
  have h2 (q : Pattern) (selected : d203806 q = 0) : d205498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203806, d205498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203806, d205498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203807 q = 0) : d205499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203807, d205499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203807, d205499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203809 q = 0) : d205501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203809, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19561 q selected
    | true =>
      simp only [d203809, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19562 q selected
  have h5 (q : Pattern) (selected : d203810 q = 0) : d205502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203810, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203810, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203811 q = 0) : d205503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203811, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203811, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203812 q = 0) : d205504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203812, d205504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203812, d205504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203817 q = 0) : d205509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203817, d205509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203817, d205509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203818 q = 0) : d205510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203818, d205510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203818, d205510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203819 q = 0) : d205511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203819, d205511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203819, d205511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19565 (p : Pattern) (selected : d203825 p = 0) : d205517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203815 q = 0) : d205507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203815, d205507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19563 q selected
    | true =>
      simp only [d203815, d205507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203816 q = 0) : d205508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203816, d205508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203816, d205508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203820 q = 0) : d205512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203820, d205512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19564 q selected
    | true =>
      simp only [d203820, d205512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203821 q = 0) : d205513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203821, d205513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203821, d205513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203822 q = 0) : d205514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203822, d205514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203822, d205514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203823 q = 0) : d205515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203823, d205515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203823, d205515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203824 q = 0) : d205516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203824, d205516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203824, d205516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203825 q = 0) : d205517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203825, d205517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203825, d205517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19566 (p : Pattern) (selected : d203827 p = 0) : d205519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203809 q = 0) : d205501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203809, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19561 q selected
    | true =>
      simp only [d203809, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19562 q selected
  have h2 (q : Pattern) (selected : d203810 q = 0) : d205502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203810, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203810, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203811 q = 0) : d205503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203811, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203811, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203817 q = 0) : d205509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203817, d205509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203817, d205509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203826 q = 0) : d205518 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203826, d205518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203826, d205518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203827 q = 0) : d205519 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203827, d205519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203827, d205519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19567 (p : Pattern) (selected : d203833 p = 0) : d205525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203820 q = 0) : d205512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203820, d205512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19564 q selected
    | true =>
      simp only [d203820, d205512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203821 q = 0) : d205513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203821, d205513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203821, d205513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203828 q = 0) : d205520 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203828, d205520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19566 q selected
    | true =>
      simp only [d203828, d205520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203829 q = 0) : d205521 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203829, d205521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203829, d205521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203830 q = 0) : d205522 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203830, d205522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203830, d205522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203831 q = 0) : d205523 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203831, d205523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203831, d205523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203832 q = 0) : d205524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203832, d205524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203832, d205524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203833 q = 0) : d205525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203833, d205525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203833, d205525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19568 (p : Pattern) (selected : d203853 p = 0) : d205485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203835 q = 0) : d205460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203835, d205460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203835, d205460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19529 q selected
  have h2 (q : Pattern) (selected : d203638 q = 0) : d205266 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203638, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19529 q selected
    | true =>
      simp only [d203638, d205266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203836 q = 0) : d205461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203836, d205461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203836, d205461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203639 q = 0) : d205267 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203639, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203639, d205267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203837 q = 0) : d205462 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203837, d205462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203837, d205462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203838 q = 0) : d205463 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203838, d205463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203838, d205463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203839 q = 0) : d205475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203839, d205475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203839, d205475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19532 q selected
  have h8 (q : Pattern) (selected : d203652 q = 0) : d205280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203652, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19532 q selected
    | true =>
      simp only [d203652, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203840 q = 0) : d205476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203840, d205476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203840, d205476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203653 q = 0) : d205281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203653, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203653, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203841 q = 0) : d205477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203841, d205477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203841, d205477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203842 q = 0) : d205478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203842, d205478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203842, d205478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203843 q = 0) : d205479 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203843, d205479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203843, d205479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203844 q = 0) : d205469 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203844, d205469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203844, d205469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19533 q selected
  have h15 (q : Pattern) (selected : d203658 q = 0) : d205286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203658, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19533 q selected
    | true =>
      simp only [d203658, d205286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203845 q = 0) : d205470 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203845, d205470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203845, d205470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203659 q = 0) : d205287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203659, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203659, d205287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203846 q = 0) : d205471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203846, d205471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203846, d205471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203847 q = 0) : d205472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203847, d205472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d203847, d205472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d203848 q = 0) : d205480 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203848, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203848, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
  have h21 (q : Pattern) (selected : d203667 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
    | true =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d203849 q = 0) : d205481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203849, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d203849, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d203668 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d203850 q = 0) : d205482 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203850, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d203850, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d203851 q = 0) : d205483 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203851, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d203851, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d203852 q = 0) : d205484 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203852, d205484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d203852, d205484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d203853 q = 0) : d205485 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203853, d205485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203853, d205485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro19569 (p : Pattern) (selected : d203856 p = 0) : d205496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203839 q = 0) : d205475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203839, d205475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203839, d205475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19532 q selected
  have h2 (q : Pattern) (selected : d203652 q = 0) : d205280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203652, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19532 q selected
    | true =>
      simp only [d203652, d205280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203840 q = 0) : d205476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203840, d205476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203840, d205476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203653 q = 0) : d205281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203653, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203653, d205281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203841 q = 0) : d205477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203841, d205477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203841, d205477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203842 q = 0) : d205478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203842, d205478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203842, d205478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203848 q = 0) : d205480 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203848, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203848, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
  have h8 (q : Pattern) (selected : d203667 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
    | true =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203849 q = 0) : d205481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203849, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203849, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203668 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203850 q = 0) : d205482 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203850, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203850, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203851 q = 0) : d205483 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203851, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203851, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203854 q = 0) : d205495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203854, d205495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203854, d205495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203855 q = 0) : d205489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203855, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203855, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203856 q = 0) : d205496 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203856, d205496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203856, d205496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19570 (p : Pattern) (selected : d203860 p = 0) : d205500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203848 q = 0) : d205480 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203848, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203848, d205480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
  have h2 (q : Pattern) (selected : d203667 q = 0) : d205295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19535 q selected
    | true =>
      simp only [d203667, d205295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203849 q = 0) : d205481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203849, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203849, d205481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203668 q = 0) : d205296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203668, d205296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203850 q = 0) : d205482 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203850, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203850, d205482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203851 q = 0) : d205483 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203851, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203851, d205483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203855 q = 0) : d205489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203855, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203855, d205489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203860 q = 0) : d205500 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203860, d205500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203860, d205500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19571 (p : Pattern) (selected : d203867 p = 0) : d205511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203857 q = 0) : d205497 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203857, d205497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19568 q selected
    | true =>
      simp only [d203857, d205497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19569 q selected
  have h2 (q : Pattern) (selected : d203858 q = 0) : d205498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203858, d205498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203858, d205498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203859 q = 0) : d205499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203859, d205499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203859, d205499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203861 q = 0) : d205501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203861, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19569 q selected
    | true =>
      simp only [d203861, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19570 q selected
  have h5 (q : Pattern) (selected : d203862 q = 0) : d205502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203862, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203862, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203863 q = 0) : d205503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203863, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203863, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203864 q = 0) : d205504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203864, d205504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203864, d205504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203865 q = 0) : d205509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203865, d205509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203865, d205509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203866 q = 0) : d205510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203866, d205510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203866, d205510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203867 q = 0) : d205511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203867, d205511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203867, d205511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19572 (p : Pattern) (selected : d203871 p = 0) : d205519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203861 q = 0) : d205501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203861, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19569 q selected
    | true =>
      simp only [d203861, d205501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19570 q selected
  have h2 (q : Pattern) (selected : d203862 q = 0) : d205502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203862, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203862, d205502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203863 q = 0) : d205503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203863, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203863, d205503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203865 q = 0) : d205509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203865, d205509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203865, d205509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203870 q = 0) : d205518 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203870, d205518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203870, d205518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203871 q = 0) : d205519 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203871, d205519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203871, d205519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19573 (p : Pattern) (selected : d203877 p = 0) : d205525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203868 q = 0) : d205512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203868, d205512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19571 q selected
    | true =>
      simp only [d203868, d205512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203869 q = 0) : d205513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203869, d205513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203869, d205513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203872 q = 0) : d205520 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203872, d205520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19572 q selected
    | true =>
      simp only [d203872, d205520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203873 q = 0) : d205521 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203873, d205521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203873, d205521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203874 q = 0) : d205522 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203874, d205522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203874, d205522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203875 q = 0) : d205523 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203875, d205523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203875, d205523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203876 q = 0) : d205524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203876, d205524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203876, d205524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203877 q = 0) : d205525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203877, d205525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203877, d205525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19574 (p : Pattern) (selected : d203881 p = 0) : d205530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203872 q = 0) : d205520 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203872, d205520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19572 q selected
    | true =>
      simp only [d203872, d205520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203873 q = 0) : d205521 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203873, d205521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203873, d205521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203878 q = 0) : d205527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203878, d205527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203878, d205527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203879 q = 0) : d205528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203879, d205528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203879, d205528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203880 q = 0) : d205529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203880, d205529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203880, d205529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203881 q = 0) : d205530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203881, d205530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203881, d205530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19575 (p : Pattern) (selected : d203887 p = 0) : d205536 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203820 q = 0) : d205512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203820, d205512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19564 q selected
    | true =>
      simp only [d203820, d205512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203821 q = 0) : d205513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203821, d205513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203821, d205513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203884 q = 0) : d205533 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203884, d205533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203884, d205533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203885 q = 0) : d205534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203885, d205534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203885, d205534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203886 q = 0) : d205535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203886, d205535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203886, d205535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203887 q = 0) : d205536 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203887, d205536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203887, d205536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19576 (p : Pattern) (selected : d203893 p = 0) : d205542 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203834 q = 0) : d205526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203834, d205526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19565 q selected
    | true =>
      simp only [d203834, d205526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19567 q selected
  have h2 (q : Pattern) (selected : d203882 q = 0) : d205531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203882, d205531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19573 q selected
    | true =>
      simp only [d203882, d205531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19574 q selected
  have h3 (q : Pattern) (selected : d203883 q = 0) : d205532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203883, d205532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203883, d205532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203888 q = 0) : d205537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203888, d205537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19575 q selected
    | true =>
      simp only [d203888, d205537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203889 q = 0) : d205538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203889, d205538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203889, d205538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203890 q = 0) : d205539 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203890, d205539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203890, d205539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203891 q = 0) : d205540 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203891, d205540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203891, d205540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203892 q = 0) : d205541 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203892, d205541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203892, d205541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203893 q = 0) : d205542 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203893, d205542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203893, d205542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19577 (p : Pattern) (selected : d203898 p = 0) : d205530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203828 q = 0) : d205520 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203828, d205520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19566 q selected
    | true =>
      simp only [d203828, d205520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203829 q = 0) : d205521 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203829, d205521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203829, d205521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203895 q = 0) : d205527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203895, d205527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203895, d205527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203896 q = 0) : d205528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203896, d205528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203896, d205528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203897 q = 0) : d205529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203897, d205529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203897, d205529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203898 q = 0) : d205530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203898, d205530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203898, d205530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19578 (p : Pattern) (selected : d203904 p = 0) : d205549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203899 q = 0) : d205544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203899, d205544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19577 q selected
    | true =>
      simp only [d203899, d205544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203900 q = 0) : d205545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203900, d205545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203900, d205545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203901 q = 0) : d205546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203901, d205546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203901, d205546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203902 q = 0) : d205547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203902, d205547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203902, d205547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203903 q = 0) : d205548 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203903, d205548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203903, d205548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203904 q = 0) : d205549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203904, d205549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203904, d205549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19579 (p : Pattern) (selected : d203910 p = 0) : d205555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203564 q = 0) : d205335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203564, d205335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203564, d205335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19511 q selected
  have h2 (q : Pattern) (selected : d203565 q = 0) : d205336 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d203565, d205336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203565, d205336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203574 q = 0) : d205345 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203574, d205345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19511 q selected
    | true =>
      simp only [d203574, d205345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19514 q selected
  have h4 (q : Pattern) (selected : d203575 q = 0) : d205346 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d203575, d205346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203575, d205346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203576 q = 0) : d205347 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d203576, d205347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203576, d205347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203737 q = 0) : d205429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203737, d205429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19544 q selected
    | true =>
      simp only [d203737, d205429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19553 q selected
  have h7 (q : Pattern) (selected : d203750 q = 0) : d205442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203750, d205442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19554 q selected
    | true =>
      simp only [d203750, d205442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19555 q selected
  have h8 (q : Pattern) (selected : d203751 q = 0) : d205443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d203751, d205443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203751, d205443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203752 q = 0) : d205444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d203752, d205444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203752, d205444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d203753 q = 0) : d205445 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d203753, d205445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203753, d205445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203757 q = 0) : d205449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203757, d205449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203757, d205449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19556 q selected
  have h12 (q : Pattern) (selected : d203759 q = 0) : d205451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203759, d205451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203759, d205451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19557 q selected
  have h13 (q : Pattern) (selected : d203760 q = 0) : d205452 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d203760, d205452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203760, d205452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203761 q = 0) : d205453 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d203761, d205453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203761, d205453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203762 q = 0) : d205454 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d203762, d205454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203762, d205454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203763 q = 0) : d205455 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d203763, d205455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203763, d205455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203894 q = 0) : d205543 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203894, d205543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203894, d205543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19576 q selected
  have h18 (q : Pattern) (selected : d203905 q = 0) : d205550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203905, d205550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203905, d205550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19578 q selected
  have h19 (q : Pattern) (selected : d203906 q = 0) : d205551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d203906, d205551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d203906, d205551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d203907 q = 0) : d205552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d203907, d205552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d203907, d205552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d203908 q = 0) : d205553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d203908, d205553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d203908, d205553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d203909 q = 0) : d205554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d203909, d205554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d203909, d205554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d203910 q = 0) : d205555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d203910, d205555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203910, d205555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro19580 (p : Pattern) (selected : d203916 p = 0) : d205561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203911 q = 0) : d205556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d203911, d205556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203911, d205556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19579 q selected
  have h2 (q : Pattern) (selected : d203912 q = 0) : d205557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d203912, d205557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203912, d205557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203913 q = 0) : d205558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d203913, d205558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203913, d205558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203914 q = 0) : d205559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d203914, d205559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203914, d205559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203915 q = 0) : d205560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d203915, d205560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203915, d205560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203916 q = 0) : d205561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d203916, d205561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203916, d205561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19581 (p : Pattern) (selected : d1999 p = 0) : d53278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d307 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1997 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1998 q = 0) : d53277 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1998, d53277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1998, d53277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1999 q = 0) : d53278 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1999, d53278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1999, d53278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19582 (p : Pattern) (selected : d2002 p = 0) : d53281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1523 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2001 q = 0) : d53280 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2002 q = 0) : d53281 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, d53281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2002, d53281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19583 (p : Pattern) (selected : d2006 p = 0) : d53285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1523 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2005 q = 0) : d53284 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d53284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2005, d53284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2006 q = 0) : d53285 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d53285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2006, d53285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19584 (p : Pattern) (selected : d203926 p = 0) : d205571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203921 q = 0) : d205566 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203921, d205566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19581 q selected
    | true =>
      simp only [d203921, d205566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19582 q selected
  have h2 (q : Pattern) (selected : d203922 q = 0) : d205567 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203922, d205567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203922, d205567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19583 q selected
  have h3 (q : Pattern) (selected : d203923 q = 0) : d205568 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203923, d205568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203923, d205568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203924 q = 0) : d205569 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203924, d205569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203924, d205569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203925 q = 0) : d205570 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203925, d205570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203925, d205570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203926 q = 0) : d205571 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203926, d205571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203926, d205571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19585 (p : Pattern) (selected : d2014 p = 0) : d53293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d307 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1997 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1998 q = 0) : d53277 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1998, d53277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1998, d53277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2013 q = 0) : d53292 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2014 q = 0) : d53293 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2014, d53293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2014, d53293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro19586 (p : Pattern) (selected : d2018 p = 0) : d53297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d307 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1997 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d128 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2016 q = 0) : d53295 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2017 q = 0) : d53296 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2017, d53296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2017, d53296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2018 q = 0) : d53297 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2018, d53297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2018, d53297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro19587 (p : Pattern) (selected : d2022 p = 0) : d53301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d128 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2016 q = 0) : d53295 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2021 q = 0) : d53300 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2021, d53300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2021, d53300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2022 q = 0) : d53301 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2022, d53301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2022, d53301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro19588 (p : Pattern) (selected : d203936 p = 0) : d205581 p = 1 := by
  have h0 (q : Pattern) (selected : d203921 q = 0) : d205566 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203921, d205566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19581 q selected
    | true =>
      simp only [d203921, d205566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19582 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203922 q = 0) : d205567 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203922, d205567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203922, d205567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19583 q selected
  have h3 (q : Pattern) (selected : d203923 q = 0) : d205568 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203923, d205568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203923, d205568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203924 q = 0) : d205569 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203924, d205569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203924, d205569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203925 q = 0) : d205570 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203925, d205570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203925, d205570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203931 q = 0) : d205576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203931, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19585 q selected
    | true =>
      simp only [d203931, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19586 q selected
  have h7 (q : Pattern) (selected : d203932 q = 0) : d205577 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203932, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203932, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19587 q selected
  have h8 (q : Pattern) (selected : d203933 q = 0) : d205578 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203933, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203933, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203934 q = 0) : d205579 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203934, d205579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203934, d205579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d203935 q = 0) : d205580 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203935, d205580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203935, d205580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d203936 q = 0) : d205581 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203936, d205581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203936, d205581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19589 (p : Pattern) (selected : d203942 p = 0) : d205587 p = 1 := by
  have h0 (q : Pattern) (selected : d203931 q = 0) : d205576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203931, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19585 q selected
    | true =>
      simp only [d203931, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19586 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203932 q = 0) : d205577 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203932, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203932, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19587 q selected
  have h3 (q : Pattern) (selected : d203933 q = 0) : d205578 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203933, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203933, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203934 q = 0) : d205579 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203934, d205579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203934, d205579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203935 q = 0) : d205580 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203935, d205580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203935, d205580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203942 q = 0) : d205587 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203942, d205587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203942, d205587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro19590 (p : Pattern) (selected : d203948 p = 0) : d205593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203927 q = 0) : d205572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203927, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19584 q selected
    | true =>
      simp only [d203927, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203928 q = 0) : d205573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203928, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203928, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203929 q = 0) : d205574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203929, d205574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203929, d205574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203930 q = 0) : d205575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203930, d205575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203930, d205575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203937 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
    | true =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203938 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203939 q = 0) : d205584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203939, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203939, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203940 q = 0) : d205585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203940, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203940, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203941 q = 0) : d205586 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203941, d205586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203941, d205586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203943 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
    | true =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203944 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203945 q = 0) : d205590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203945, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203945, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203946 q = 0) : d205591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203946, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203946, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d203947 q = 0) : d205592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203947, d205592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203947, d205592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d203948 q = 0) : d205593 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203948, d205593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203948, d205593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19591 (p : Pattern) (selected : d2027 p = 0) : d53306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d307 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1997 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2013 q = 0) : d53292 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2027 q = 0) : d53306 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19592 (p : Pattern) (selected : d203953 p = 0) : d205598 p = 1 := by
  have h0 (q : Pattern) (selected : d203931 q = 0) : d205576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203931, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19585 q selected
    | true =>
      simp only [d203931, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19586 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203932 q = 0) : d205577 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203932, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203932, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19587 q selected
  have h3 (q : Pattern) (selected : d203933 q = 0) : d205578 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203933, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203933, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203949 q = 0) : d205594 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203949, d205594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19591 q selected
    | true =>
      simp only [d203949, d205594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203950 q = 0) : d205595 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203950, d205595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203950, d205595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d203951 q = 0) : d205596 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203951, d205596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203951, d205596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203952 q = 0) : d205597 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203952, d205597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203952, d205597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d203953 q = 0) : d205598 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203953, d205598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203953, d205598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro19593 (p : Pattern) (selected : d203960 p = 0) : d205605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203937 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
    | true =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203938 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203939 q = 0) : d205584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203939, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203939, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203940 q = 0) : d205585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203940, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203940, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203954 q = 0) : d205599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203954, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19592 q selected
    | true =>
      simp only [d203954, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203955 q = 0) : d205600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203955, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203955, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203956 q = 0) : d205601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203956, d205601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203956, d205601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203957 q = 0) : d205602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203957, d205602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203957, d205602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203958 q = 0) : d205603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203958, d205603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203958, d205603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203943 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
    | true =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203944 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203945 q = 0) : d205590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203945, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203945, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203946 q = 0) : d205591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203946, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203946, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d203959 q = 0) : d205604 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203959, d205604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203959, d205604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203960 q = 0) : d205605 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203960, d205605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203960, d205605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19594 (p : Pattern) (selected : d203965 p = 0) : d205610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203954 q = 0) : d205599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203954, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19592 q selected
    | true =>
      simp only [d203954, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203955 q = 0) : d205600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203955, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203955, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203956 q = 0) : d205601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203956, d205601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203956, d205601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203957 q = 0) : d205602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203957, d205602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203957, d205602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203964 q = 0) : d205609 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203964, d205609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203964, d205609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203965 q = 0) : d205610 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203965, d205610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203965, d205610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19595 (p : Pattern) (selected : d203972 p = 0) : d205617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203961 q = 0) : d205606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203961, d205606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19590 q selected
    | true =>
      simp only [d203961, d205606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19593 q selected
  have h2 (q : Pattern) (selected : d203962 q = 0) : d205607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203962, d205607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203962, d205607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203963 q = 0) : d205608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203963, d205608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203963, d205608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203966 q = 0) : d205611 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203966, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19593 q selected
    | true =>
      simp only [d203966, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19594 q selected
  have h5 (q : Pattern) (selected : d203967 q = 0) : d205612 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203967, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203967, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203968 q = 0) : d205613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203968, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203968, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203969 q = 0) : d205614 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203969, d205614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203969, d205614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203970 q = 0) : d205615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203970, d205615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203970, d205615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203971 q = 0) : d205616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203971, d205616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203971, d205616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203972 q = 0) : d205617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203972, d205617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203972, d205617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19596 (p : Pattern) (selected : d203976 p = 0) : d205621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203966 q = 0) : d205611 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203966, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19593 q selected
    | true =>
      simp only [d203966, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19594 q selected
  have h2 (q : Pattern) (selected : d203967 q = 0) : d205612 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203967, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203967, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203968 q = 0) : d205613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203968, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203968, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203970 q = 0) : d205615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203970, d205615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203970, d205615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203975 q = 0) : d205620 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203975, d205620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203975, d205620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203976 q = 0) : d205621 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203976, d205621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203976, d205621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19597 (p : Pattern) (selected : d203982 p = 0) : d205627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203979 q = 0) : d205624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203980 q = 0) : d205625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203980, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203980, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203981 q = 0) : d205626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203981, d205626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203981, d205626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203982 q = 0) : d205627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203982, d205627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203982, d205627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19598 (p : Pattern) (selected : d203986 p = 0) : d205631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203983 q = 0) : d205628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203984 q = 0) : d205629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203984, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203984, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203985 q = 0) : d205630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203985, d205630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203985, d205630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203986 q = 0) : d205631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203986, d205631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203986, d205631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19599 (p : Pattern) (selected : d203992 p = 0) : d205637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203987 q = 0) : d205632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203987, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19597 q selected
    | true =>
      simp only [d203987, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19598 q selected
  have h2 (q : Pattern) (selected : d203988 q = 0) : d205633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203988, d205633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203988, d205633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203989 q = 0) : d205634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203989, d205634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203989, d205634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203990 q = 0) : d205635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203990, d205635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203990, d205635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203991 q = 0) : d205636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203991, d205636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203991, d205636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203992 q = 0) : d205637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203992, d205637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203992, d205637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19600 (p : Pattern) (selected : d203995 p = 0) : d205640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203979 q = 0) : d205624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203980 q = 0) : d205625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203980, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203980, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203981 q = 0) : d205626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203981, d205626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203981, d205626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203995 q = 0) : d205640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203995, d205640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203995, d205640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19601 (p : Pattern) (selected : d203996 p = 0) : d205641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203983 q = 0) : d205628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203984 q = 0) : d205629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203984, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203984, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203985 q = 0) : d205630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203985, d205630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203985, d205630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203996 q = 0) : d205641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203996, d205641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203996, d205641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19602 (p : Pattern) (selected : d204002 p = 0) : d205647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203987 q = 0) : d205632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203987, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19597 q selected
    | true =>
      simp only [d203987, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19598 q selected
  have h2 (q : Pattern) (selected : d203988 q = 0) : d205633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203988, d205633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203988, d205633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203989 q = 0) : d205634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203989, d205634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203989, d205634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203990 q = 0) : d205635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203990, d205635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203990, d205635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203991 q = 0) : d205636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203991, d205636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203991, d205636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203997 q = 0) : d205642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203997, d205642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19600 q selected
    | true =>
      simp only [d203997, d205642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19601 q selected
  have h7 (q : Pattern) (selected : d203998 q = 0) : d205643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203998, d205643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203998, d205643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203999 q = 0) : d205644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203999, d205644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203999, d205644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204000 q = 0) : d205645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204000, d205645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204000, d205645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204001 q = 0) : d205646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204001, d205646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204001, d205646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204002 q = 0) : d205647 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204002, d205647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204002, d205647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19603 (p : Pattern) (selected : d204007 p = 0) : d205652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203979 q = 0) : d205624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203980 q = 0) : d205625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203980, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203980, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204006 q = 0) : d205651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204006, d205651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204006, d205651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204007 q = 0) : d205652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204007, d205652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204007, d205652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19604 (p : Pattern) (selected : d204009 p = 0) : d205654 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203983 q = 0) : d205628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203984 q = 0) : d205629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203984, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203984, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204008 q = 0) : d205653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204008, d205653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204008, d205653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204009 q = 0) : d205654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204009, d205654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204009, d205654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19605 (p : Pattern) (selected : d204016 p = 0) : d205661 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203979 q = 0) : d205624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204014 q = 0) : d205659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204014, d205659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204014, d205659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204015 q = 0) : d205660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204015, d205660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204015, d205660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204016 q = 0) : d205661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204016, d205661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204016, d205661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19606 (p : Pattern) (selected : d204019 p = 0) : d205664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203983 q = 0) : d205628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204017 q = 0) : d205662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204017, d205662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204017, d205662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204018 q = 0) : d205663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204018, d205663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204018, d205663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204019 q = 0) : d205664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204019, d205664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204019, d205664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19607 (p : Pattern) (selected : d204024 p = 0) : d205669 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203927 q = 0) : d205572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203927, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19584 q selected
    | true =>
      simp only [d203927, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203928 q = 0) : d205573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203928, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203928, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203929 q = 0) : d205574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203929, d205574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203929, d205574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203930 q = 0) : d205575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203930, d205575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203930, d205575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204023 q = 0) : d205668 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204023, d205668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204023, d205668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203937 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
    | true =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203938 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203939 q = 0) : d205584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203939, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203939, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203940 q = 0) : d205585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203940, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203940, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d203941 q = 0) : d205586 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203941, d205586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203941, d205586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204024 q = 0) : d205669 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204024, d205669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204024, d205669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19608 (p : Pattern) (selected : d204028 p = 0) : d205673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203937 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
    | true =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203938 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203939 q = 0) : d205584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203939, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203939, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203940 q = 0) : d205585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203940, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203940, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203943 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
    | true =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203944 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203945 q = 0) : d205590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203945, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203945, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203946 q = 0) : d205591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203946, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203946, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203947 q = 0) : d205592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203947, d205592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203947, d205592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203959 q = 0) : d205604 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203959, d205604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203959, d205604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d204028 q = 0) : d205673 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204028, d205673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204028, d205673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19609 (p : Pattern) (selected : d204034 p = 0) : d205679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204025 q = 0) : d205670 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204025, d205670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19607 q selected
    | true =>
      simp only [d204025, d205670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19590 q selected
  have h2 (q : Pattern) (selected : d204026 q = 0) : d205671 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204026, d205671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204026, d205671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204027 q = 0) : d205672 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204027, d205672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204027, d205672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204029 q = 0) : d205674 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204029, d205674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19590 q selected
    | true =>
      simp only [d204029, d205674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19608 q selected
  have h5 (q : Pattern) (selected : d204030 q = 0) : d205675 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204030, d205675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204030, d205675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204031 q = 0) : d205676 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204031, d205676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204031, d205676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204032 q = 0) : d205677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204032, d205677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204032, d205677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203961 q = 0) : d205606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203961, d205606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19590 q selected
    | true =>
      simp only [d203961, d205606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19593 q selected
  have h9 (q : Pattern) (selected : d203962 q = 0) : d205607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203962, d205607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203962, d205607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203963 q = 0) : d205608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203963, d205608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203963, d205608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203966 q = 0) : d205611 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203966, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19593 q selected
    | true =>
      simp only [d203966, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19594 q selected
  have h12 (q : Pattern) (selected : d203967 q = 0) : d205612 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203967, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203967, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203968 q = 0) : d205613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203968, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203968, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203969 q = 0) : d205614 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203969, d205614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203969, d205614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d204033 q = 0) : d205678 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d204033, d205678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204033, d205678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d204034 q = 0) : d205679 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d204034, d205679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d204034, d205679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro19610 (p : Pattern) (selected : d204040 p = 0) : d205685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204035 q = 0) : d205680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204035, d205680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19609 q selected
    | true =>
      simp only [d204035, d205680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204036 q = 0) : d205681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204036, d205681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204036, d205681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204037 q = 0) : d205682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204037, d205682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204037, d205682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204038 q = 0) : d205683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204038, d205683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204038, d205683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204039 q = 0) : d205684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204039, d205684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204039, d205684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204040 q = 0) : d205685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204040, d205685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204040, d205685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19611 (p : Pattern) (selected : d2165 p = 0) : d53278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2164 q = 0) : d53277 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2164, d53277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2164, d53277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2165 q = 0) : d53278 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2165, d53278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2165, d53278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19612 (p : Pattern) (selected : d2168 p = 0) : d53281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2167 q = 0) : d53280 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2167, d53280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2167, d53280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2168 q = 0) : d53281 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2168, d53281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2168, d53281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19613 (p : Pattern) (selected : d2172 p = 0) : d53285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2171 q = 0) : d53284 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2171, d53284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2171, d53284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2172 q = 0) : d53285 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2172, d53285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2172, d53285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19614 (p : Pattern) (selected : d204047 p = 0) : d205571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204042 q = 0) : d205566 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204042, d205566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19611 q selected
    | true =>
      simp only [d204042, d205566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19612 q selected
  have h2 (q : Pattern) (selected : d204043 q = 0) : d205567 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204043, d205567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204043, d205567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
  have h3 (q : Pattern) (selected : d204044 q = 0) : d205568 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204044, d205568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204044, d205568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204045 q = 0) : d205569 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d204045, d205569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204045, d205569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204046 q = 0) : d205570 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d204046, d205570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204046, d205570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204047 q = 0) : d205571 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d204047, d205571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204047, d205571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19615 (p : Pattern) (selected : d2180 p = 0) : d53293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2164 q = 0) : d53277 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2164, d53277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2164, d53277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2179 q = 0) : d53292 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2179, d53292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2179, d53292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2180 q = 0) : d53293 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2180, d53293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2180, d53293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro19616 (p : Pattern) (selected : d2184 p = 0) : d53297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d339 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2182 q = 0) : d53295 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2182, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2182, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2183 q = 0) : d53296 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2183, d53296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2183, d53296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2184 q = 0) : d53297 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2184, d53297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2184, d53297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro19617 (p : Pattern) (selected : d2188 p = 0) : d53301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2182 q = 0) : d53295 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2182, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2182, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2187 q = 0) : d53300 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2187, d53300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2187, d53300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2188 q = 0) : d53301 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2188, d53301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2188, d53301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro19618 (p : Pattern) (selected : d204057 p = 0) : d205581 p = 1 := by
  have h0 (q : Pattern) (selected : d204042 q = 0) : d205566 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204042, d205566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19611 q selected
    | true =>
      simp only [d204042, d205566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19612 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d204043 q = 0) : d205567 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204043, d205567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204043, d205567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
  have h3 (q : Pattern) (selected : d204044 q = 0) : d205568 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204044, d205568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204044, d205568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204045 q = 0) : d205569 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d204045, d205569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204045, d205569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d204046 q = 0) : d205570 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d204046, d205570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204046, d205570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d204052 q = 0) : d205576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204052, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19615 q selected
    | true =>
      simp only [d204052, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19616 q selected
  have h7 (q : Pattern) (selected : d204053 q = 0) : d205577 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204053, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204053, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19617 q selected
  have h8 (q : Pattern) (selected : d204054 q = 0) : d205578 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204054, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204054, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d204055 q = 0) : d205579 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d204055, d205579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d204055, d205579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d204056 q = 0) : d205580 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d204056, d205580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204056, d205580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d204057 q = 0) : d205581 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d204057, d205581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204057, d205581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19619 (p : Pattern) (selected : d204063 p = 0) : d205587 p = 1 := by
  have h0 (q : Pattern) (selected : d204052 q = 0) : d205576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204052, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19615 q selected
    | true =>
      simp only [d204052, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19616 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d204053 q = 0) : d205577 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204053, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204053, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19617 q selected
  have h3 (q : Pattern) (selected : d204054 q = 0) : d205578 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204054, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204054, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204055 q = 0) : d205579 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d204055, d205579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204055, d205579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d204056 q = 0) : d205580 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d204056, d205580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204056, d205580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d204063 q = 0) : d205587 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d204063, d205587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204063, d205587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro19620 (p : Pattern) (selected : d204069 p = 0) : d205593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204048 q = 0) : d205572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204048, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19614 q selected
    | true =>
      simp only [d204048, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204049 q = 0) : d205573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204049, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204049, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204050 q = 0) : d205574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204050, d205574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204050, d205574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204051 q = 0) : d205575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204051, d205575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204051, d205575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204058 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204058, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19618 q selected
    | true =>
      simp only [d204058, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204059 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204059, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204059, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204060 q = 0) : d205584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204060, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204060, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204061 q = 0) : d205585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204061, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204061, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204062 q = 0) : d205586 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204062, d205586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204062, d205586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204064 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204064, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19619 q selected
    | true =>
      simp only [d204064, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d204065 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204065, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d204065, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d204066 q = 0) : d205590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204066, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204066, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d204067 q = 0) : d205591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204067, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d204067, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d204068 q = 0) : d205592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204068, d205592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d204068, d205592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d204069 q = 0) : d205593 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204069, d205593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204069, d205593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19621 (p : Pattern) (selected : d2193 p = 0) : d53306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2179 q = 0) : d53292 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2179, d53292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2179, d53292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2193 q = 0) : d53306 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2193, d53306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2193, d53306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19622 (p : Pattern) (selected : d204074 p = 0) : d205598 p = 1 := by
  have h0 (q : Pattern) (selected : d204052 q = 0) : d205576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204052, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19615 q selected
    | true =>
      simp only [d204052, d205576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19616 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d204053 q = 0) : d205577 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204053, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204053, d205577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19617 q selected
  have h3 (q : Pattern) (selected : d204054 q = 0) : d205578 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204054, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204054, d205578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204070 q = 0) : d205594 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204070, d205594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19621 q selected
    | true =>
      simp only [d204070, d205594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d204071 q = 0) : d205595 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204071, d205595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204071, d205595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d204072 q = 0) : d205596 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d204072, d205596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204072, d205596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204073 q = 0) : d205597 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d204073, d205597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204073, d205597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d204074 q = 0) : d205598 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d204074, d205598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204074, d205598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro19623 (p : Pattern) (selected : d204081 p = 0) : d205605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204058 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204058, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19618 q selected
    | true =>
      simp only [d204058, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204059 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204059, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204059, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204060 q = 0) : d205584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204060, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204060, d205584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204061 q = 0) : d205585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204061, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204061, d205585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204075 q = 0) : d205599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204075, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19622 q selected
    | true =>
      simp only [d204075, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204076 q = 0) : d205600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204076, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204076, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204077 q = 0) : d205601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204077, d205601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204077, d205601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204078 q = 0) : d205602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204078, d205602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204078, d205602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204079 q = 0) : d205603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204079, d205603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204079, d205603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204064 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204064, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19619 q selected
    | true =>
      simp only [d204064, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d204065 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204065, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d204065, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d204066 q = 0) : d205590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204066, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204066, d205590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d204067 q = 0) : d205591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204067, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d204067, d205591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d204080 q = 0) : d205604 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204080, d205604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d204080, d205604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d204081 q = 0) : d205605 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204081, d205605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204081, d205605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19624 (p : Pattern) (selected : d204086 p = 0) : d205610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204075 q = 0) : d205599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204075, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19622 q selected
    | true =>
      simp only [d204075, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204076 q = 0) : d205600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204076, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204076, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204077 q = 0) : d205601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204077, d205601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204077, d205601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204078 q = 0) : d205602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204078, d205602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204078, d205602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204085 q = 0) : d205609 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204085, d205609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204085, d205609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204086 q = 0) : d205610 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204086, d205610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204086, d205610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19625 (p : Pattern) (selected : d204093 p = 0) : d205617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204082 q = 0) : d205606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204082, d205606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19620 q selected
    | true =>
      simp only [d204082, d205606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19623 q selected
  have h2 (q : Pattern) (selected : d204083 q = 0) : d205607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204083, d205607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204083, d205607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204084 q = 0) : d205608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204084, d205608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204084, d205608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204087 q = 0) : d205611 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204087, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19623 q selected
    | true =>
      simp only [d204087, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19624 q selected
  have h5 (q : Pattern) (selected : d204088 q = 0) : d205612 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204088, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204088, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204089 q = 0) : d205613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204089, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204089, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204090 q = 0) : d205614 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204090, d205614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204090, d205614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204091 q = 0) : d205615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204091, d205615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204091, d205615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204092 q = 0) : d205616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d204092, d205616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204092, d205616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204093 q = 0) : d205617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d204093, d205617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204093, d205617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19626 (p : Pattern) (selected : d204097 p = 0) : d205621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204087 q = 0) : d205611 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204087, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19623 q selected
    | true =>
      simp only [d204087, d205611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19624 q selected
  have h2 (q : Pattern) (selected : d204088 q = 0) : d205612 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204088, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204088, d205612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204089 q = 0) : d205613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204089, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204089, d205613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204091 q = 0) : d205615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204091, d205615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204091, d205615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204096 q = 0) : d205620 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d204096, d205620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204096, d205620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204097 q = 0) : d205621 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d204097, d205621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204097, d205621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19627 (p : Pattern) (selected : d204103 p = 0) : d205627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204094 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204094, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19625 q selected
    | true =>
      simp only [d204094, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204095 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204095, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204095, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204098 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204098, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19626 q selected
    | true =>
      simp only [d204098, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204099 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204099, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204099, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204100 q = 0) : d205624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204100, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204100, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204101 q = 0) : d205625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204101, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204101, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204102 q = 0) : d205626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204102, d205626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204102, d205626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204103 q = 0) : d205627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204103, d205627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204103, d205627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19628 (p : Pattern) (selected : d204107 p = 0) : d205631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204098 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204098, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19626 q selected
    | true =>
      simp only [d204098, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204099 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204099, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204099, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204104 q = 0) : d205628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204104, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204104, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204105 q = 0) : d205629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204105, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204105, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204106 q = 0) : d205630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204106, d205630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204106, d205630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204107 q = 0) : d205631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204107, d205631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204107, d205631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19629 (p : Pattern) (selected : d204113 p = 0) : d205691 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204110 q = 0) : d205688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204110, d205688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204110, d205688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204111 q = 0) : d205689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204111, d205689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204111, d205689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204112 q = 0) : d205690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204112, d205690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204112, d205690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204113 q = 0) : d205691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204113, d205691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204113, d205691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19630 (p : Pattern) (selected : d204119 p = 0) : d205697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204010 q = 0) : d205655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204010, d205655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19603 q selected
    | true =>
      simp only [d204010, d205655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19604 q selected
  have h2 (q : Pattern) (selected : d204011 q = 0) : d205656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204011, d205656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204011, d205656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204012 q = 0) : d205657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204012, d205657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204012, d205657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204013 q = 0) : d205658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204013, d205658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204013, d205658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204020 q = 0) : d205665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204020, d205665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19605 q selected
    | true =>
      simp only [d204020, d205665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19606 q selected
  have h6 (q : Pattern) (selected : d204021 q = 0) : d205666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204021, d205666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204021, d205666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204022 q = 0) : d205667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204022, d205667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204022, d205667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204041 q = 0) : d205686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204041, d205686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19610 q selected
    | true =>
      simp only [d204041, d205686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19597 q selected
  have h9 (q : Pattern) (selected : d204108 q = 0) : d205632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204108, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19627 q selected
    | true =>
      simp only [d204108, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19628 q selected
  have h10 (q : Pattern) (selected : d204109 q = 0) : d205687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204109, d205687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d204109, d205687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204114 q = 0) : d205692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204114, d205692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19629 q selected
    | true =>
      simp only [d204114, d205692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d204115 q = 0) : d205693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204115, d205693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d204115, d205693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d204116 q = 0) : d205694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204116, d205694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d204116, d205694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204117 q = 0) : d205695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204117, d205695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204117, d205695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d204118 q = 0) : d205696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204118, d205696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204118, d205696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d204119 q = 0) : d205697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204119, d205697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204119, d205697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro19631 (p : Pattern) (selected : d204120 p = 0) : d205698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203979 q = 0) : d205624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203980 q = 0) : d205625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203980, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203980, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204006 q = 0) : d205651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204006, d205651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204006, d205651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204120 q = 0) : d205698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204120, d205698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204120, d205698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19632 (p : Pattern) (selected : d204121 p = 0) : d205699 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203983 q = 0) : d205628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203984 q = 0) : d205629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203984, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203984, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204008 q = 0) : d205653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204008, d205653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204008, d205653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204121 q = 0) : d205699 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204121, d205699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204121, d205699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19633 (p : Pattern) (selected : d204126 p = 0) : d205704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203979 q = 0) : d205624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203979, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204014 q = 0) : d205659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204014, d205659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204014, d205659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204015 q = 0) : d205660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204015, d205660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204015, d205660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204126 q = 0) : d205704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204126, d205704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204126, d205704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19634 (p : Pattern) (selected : d204127 p = 0) : d205705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203977 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19596 q selected
    | true =>
      simp only [d203977, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203978 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203978, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203983 q = 0) : d205628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203983, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204017 q = 0) : d205662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204017, d205662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204017, d205662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204018 q = 0) : d205663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204018, d205663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204018, d205663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204127 q = 0) : d205705 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204127, d205705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204127, d205705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19635 (p : Pattern) (selected : d204131 p = 0) : d205709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204035 q = 0) : d205680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204035, d205680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19609 q selected
    | true =>
      simp only [d204035, d205680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204036 q = 0) : d205681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204036, d205681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204036, d205681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204037 q = 0) : d205682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204037, d205682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204037, d205682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204038 q = 0) : d205683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204038, d205683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204038, d205683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204039 q = 0) : d205684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204039, d205684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204039, d205684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204131 q = 0) : d205709 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204131, d205709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204131, d205709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19636 (p : Pattern) (selected : d204133 p = 0) : d205640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204094 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204094, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19625 q selected
    | true =>
      simp only [d204094, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204095 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204095, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204095, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204098 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204098, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19626 q selected
    | true =>
      simp only [d204098, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204099 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204099, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204099, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204100 q = 0) : d205624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204100, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204100, d205624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204101 q = 0) : d205625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204101, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204101, d205625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204102 q = 0) : d205626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204102, d205626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204102, d205626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204133 q = 0) : d205640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204133, d205640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204133, d205640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19637 (p : Pattern) (selected : d204134 p = 0) : d205641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204098 q = 0) : d205622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204098, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19626 q selected
    | true =>
      simp only [d204098, d205622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204099 q = 0) : d205623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204099, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204099, d205623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204104 q = 0) : d205628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204104, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204104, d205628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204105 q = 0) : d205629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204105, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204105, d205629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204106 q = 0) : d205630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204106, d205630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204106, d205630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204134 q = 0) : d205641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204134, d205641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204134, d205641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19638 (p : Pattern) (selected : d204137 p = 0) : d205712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203973 q = 0) : d205618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19595 q selected
    | true =>
      simp only [d203973, d205618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203974 q = 0) : d205619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203974, d205619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204110 q = 0) : d205688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204110, d205688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204110, d205688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204111 q = 0) : d205689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204111, d205689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204111, d205689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204112 q = 0) : d205690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204112, d205690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204112, d205690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204137 q = 0) : d205712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204137, d205712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204137, d205712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19639 (p : Pattern) (selected : d204143 p = 0) : d205718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204010 q = 0) : d205655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204010, d205655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19603 q selected
    | true =>
      simp only [d204010, d205655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19604 q selected
  have h2 (q : Pattern) (selected : d204011 q = 0) : d205656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204011, d205656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204011, d205656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204012 q = 0) : d205657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204012, d205657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204012, d205657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204013 q = 0) : d205658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204013, d205658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204013, d205658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204020 q = 0) : d205665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204020, d205665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19605 q selected
    | true =>
      simp only [d204020, d205665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19606 q selected
  have h6 (q : Pattern) (selected : d204021 q = 0) : d205666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204021, d205666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204021, d205666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204022 q = 0) : d205667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204022, d205667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204022, d205667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204041 q = 0) : d205686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204041, d205686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19610 q selected
    | true =>
      simp only [d204041, d205686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19597 q selected
  have h9 (q : Pattern) (selected : d204108 q = 0) : d205632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204108, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19627 q selected
    | true =>
      simp only [d204108, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19628 q selected
  have h10 (q : Pattern) (selected : d204109 q = 0) : d205687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204109, d205687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d204109, d205687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204114 q = 0) : d205692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204114, d205692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19629 q selected
    | true =>
      simp only [d204114, d205692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d204115 q = 0) : d205693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204115, d205693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d204115, d205693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d204116 q = 0) : d205694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204116, d205694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d204116, d205694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204117 q = 0) : d205695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204117, d205695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204117, d205695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d204118 q = 0) : d205696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204118, d205696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204118, d205696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d204122 q = 0) : d205700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204122, d205700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19631 q selected
    | true =>
      simp only [d204122, d205700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19632 q selected
  have h17 (q : Pattern) (selected : d204123 q = 0) : d205701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204123, d205701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204123, d205701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d204124 q = 0) : d205702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204124, d205702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d204124, d205702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d204125 q = 0) : d205703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204125, d205703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204125, d205703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d204128 q = 0) : d205706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204128, d205706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19633 q selected
    | true =>
      simp only [d204128, d205706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19634 q selected
  have h21 (q : Pattern) (selected : d204129 q = 0) : d205707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204129, d205707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204129, d205707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d204130 q = 0) : d205708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204130, d205708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d204130, d205708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d204132 q = 0) : d205710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204132, d205710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19635 q selected
    | true =>
      simp only [d204132, d205710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19600 q selected
  have h24 (q : Pattern) (selected : d204135 q = 0) : d205642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204135, d205642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19636 q selected
    | true =>
      simp only [d204135, d205642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19637 q selected
  have h25 (q : Pattern) (selected : d204136 q = 0) : d205711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204136, d205711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d204136, d205711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d204138 q = 0) : d205713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204138, d205713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19638 q selected
    | true =>
      simp only [d204138, d205713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d204139 q = 0) : d205714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204139, d205714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d204139, d205714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d204140 q = 0) : d205715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204140, d205715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d204140, d205715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d204141 q = 0) : d205716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204141, d205716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d204141, d205716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d204142 q = 0) : d205717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204142, d205717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d204142, d205717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d204143 q = 0) : d205718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204143, d205718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d204143, d205718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro19640 (p : Pattern) (selected : d204150 p = 0) : d205725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203987 q = 0) : d205632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203987, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19597 q selected
    | true =>
      simp only [d203987, d205632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19598 q selected
  have h2 (q : Pattern) (selected : d203988 q = 0) : d205633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203988, d205633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203988, d205633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203989 q = 0) : d205634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203989, d205634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203989, d205634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203990 q = 0) : d205635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203990, d205635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203990, d205635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203991 q = 0) : d205636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203991, d205636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203991, d205636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204145 q = 0) : d205720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204145, d205720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19598 q selected
    | true =>
      simp only [d204145, d205720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204146 q = 0) : d205721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204146, d205721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204146, d205721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204147 q = 0) : d205722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204147, d205722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204147, d205722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204148 q = 0) : d205723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204148, d205723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204148, d205723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204149 q = 0) : d205724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204149, d205724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204149, d205724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204150 q = 0) : d205725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204150, d205725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204150, d205725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19641 (p : Pattern) (selected : d204156 p = 0) : d205731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204145 q = 0) : d205720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204145, d205720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19598 q selected
    | true =>
      simp only [d204145, d205720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204146 q = 0) : d205721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204146, d205721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204146, d205721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204147 q = 0) : d205722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204147, d205722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204147, d205722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204148 q = 0) : d205723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204148, d205723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204148, d205723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204149 q = 0) : d205724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204149, d205724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204149, d205724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204151 q = 0) : d205726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204151, d205726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19601 q selected
    | true =>
      simp only [d204151, d205726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204152 q = 0) : d205727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204152, d205727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204152, d205727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204153 q = 0) : d205728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204153, d205728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204153, d205728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204154 q = 0) : d205729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204154, d205729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204154, d205729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204155 q = 0) : d205730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204155, d205730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204155, d205730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204156 q = 0) : d205731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204156, d205731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204156, d205731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19642 (p : Pattern) (selected : d204163 p = 0) : d205738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204132 q = 0) : d205710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204132, d205710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19635 q selected
    | true =>
      simp only [d204132, d205710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19600 q selected
  have h2 (q : Pattern) (selected : d204135 q = 0) : d205642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204135, d205642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19636 q selected
    | true =>
      simp only [d204135, d205642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19637 q selected
  have h3 (q : Pattern) (selected : d204136 q = 0) : d205711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204136, d205711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204136, d205711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204138 q = 0) : d205713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204138, d205713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19638 q selected
    | true =>
      simp only [d204138, d205713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204139 q = 0) : d205714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204139, d205714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204139, d205714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204140 q = 0) : d205715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204140, d205715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204140, d205715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204161 q = 0) : d205736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204161, d205736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204161, d205736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204162 q = 0) : d205737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204162, d205737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204162, d205737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d204163 q = 0) : d205738 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204163, d205738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204163, d205738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19643 (p : Pattern) (selected : d204165 p = 0) : d205740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204151 q = 0) : d205726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204151, d205726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19601 q selected
    | true =>
      simp only [d204151, d205726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204152 q = 0) : d205727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204152, d205727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204152, d205727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204153 q = 0) : d205728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204153, d205728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204153, d205728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204154 q = 0) : d205729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204154, d205729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204154, d205729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204155 q = 0) : d205730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204155, d205730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204155, d205730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204165 q = 0) : d205740 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204165, d205740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204165, d205740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19644 (p : Pattern) (selected : d204181 p = 0) : d205756 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204171 q = 0) : d205746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204171, d205746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204171, d205746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19584 q selected
  have h2 (q : Pattern) (selected : d203927 q = 0) : d205572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203927, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19584 q selected
    | true =>
      simp only [d203927, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204172 q = 0) : d205747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204172, d205747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204172, d205747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203928 q = 0) : d205573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203928, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203928, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204173 q = 0) : d205748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204173, d205748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204173, d205748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204174 q = 0) : d205749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204174, d205749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204174, d205749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204175 q = 0) : d205750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204175, d205750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204175, d205750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204176 q = 0) : d205751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204176, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204176, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
  have h9 (q : Pattern) (selected : d203937 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
    | true =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d204177 q = 0) : d205752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204177, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d204177, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d203938 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d204178 q = 0) : d205753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204178, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d204178, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d204179 q = 0) : d205754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204179, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d204179, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d204180 q = 0) : d205755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204180, d205755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204180, d205755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d204181 q = 0) : d205756 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204181, d205756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204181, d205756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19645 (p : Pattern) (selected : d204187 p = 0) : d205762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204171 q = 0) : d205746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204171, d205746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204171, d205746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19584 q selected
  have h2 (q : Pattern) (selected : d203927 q = 0) : d205572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203927, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19584 q selected
    | true =>
      simp only [d203927, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204172 q = 0) : d205747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204172, d205747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204172, d205747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203928 q = 0) : d205573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203928, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203928, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204173 q = 0) : d205748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204173, d205748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204173, d205748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204174 q = 0) : d205749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204174, d205749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204174, d205749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204176 q = 0) : d205751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204176, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204176, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
  have h8 (q : Pattern) (selected : d203937 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
    | true =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204177 q = 0) : d205752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204177, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204177, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203938 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d204178 q = 0) : d205753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204178, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204178, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d204179 q = 0) : d205754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204179, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d204179, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d204180 q = 0) : d205755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204180, d205755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204180, d205755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204182 q = 0) : d205757 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204182, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204182, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
  have h15 (q : Pattern) (selected : d203943 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
    | true =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d204183 q = 0) : d205758 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204183, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d204183, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203944 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d204184 q = 0) : d205759 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204184, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d204184, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d204185 q = 0) : d205760 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204185, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d204185, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d204186 q = 0) : d205761 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204186, d205761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d204186, d205761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d204187 q = 0) : d205762 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204187, d205762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d204187, d205762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro19646 (p : Pattern) (selected : d204192 p = 0) : d205767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204176 q = 0) : d205751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204176, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204176, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
  have h2 (q : Pattern) (selected : d203937 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
    | true =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204177 q = 0) : d205752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204177, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204177, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203938 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204178 q = 0) : d205753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204178, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204178, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204179 q = 0) : d205754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204179, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204179, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204182 q = 0) : d205757 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204182, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204182, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
  have h8 (q : Pattern) (selected : d203943 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
    | true =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204183 q = 0) : d205758 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204183, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204183, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203944 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d204184 q = 0) : d205759 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204184, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204184, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d204185 q = 0) : d205760 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204185, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d204185, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d204186 q = 0) : d205761 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204186, d205761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204186, d205761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204191 q = 0) : d205766 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204191, d205766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d204191, d205766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d204192 q = 0) : d205767 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204192, d205767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d204192, d205767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19647 (p : Pattern) (selected : d204202 p = 0) : d205777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204176 q = 0) : d205751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204176, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204176, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
  have h2 (q : Pattern) (selected : d203937 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19588 q selected
    | true =>
      simp only [d203937, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204177 q = 0) : d205752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204177, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204177, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203938 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203938, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204178 q = 0) : d205753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204178, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204178, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204179 q = 0) : d205754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204179, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204179, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204197 q = 0) : d205772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204197, d205772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204197, d205772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19592 q selected
  have h8 (q : Pattern) (selected : d203954 q = 0) : d205599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203954, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19592 q selected
    | true =>
      simp only [d203954, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204198 q = 0) : d205773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204198, d205773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204198, d205773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203955 q = 0) : d205600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203955, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203955, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d204199 q = 0) : d205774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204199, d205774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204199, d205774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d204200 q = 0) : d205775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204200, d205775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d204200, d205775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d204201 q = 0) : d205776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204201, d205776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204201, d205776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204182 q = 0) : d205757 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204182, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204182, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
  have h15 (q : Pattern) (selected : d203943 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19589 q selected
    | true =>
      simp only [d203943, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d204183 q = 0) : d205758 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204183, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d204183, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203944 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203944, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d204184 q = 0) : d205759 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204184, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d204184, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d204185 q = 0) : d205760 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204185, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d204185, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d204191 q = 0) : d205766 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204191, d205766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d204191, d205766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d204202 q = 0) : d205777 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204202, d205777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d204202, d205777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro19648 (p : Pattern) (selected : d204207 p = 0) : d205782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204197 q = 0) : d205772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204197, d205772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204197, d205772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19592 q selected
  have h2 (q : Pattern) (selected : d203954 q = 0) : d205599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203954, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19592 q selected
    | true =>
      simp only [d203954, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204198 q = 0) : d205773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204198, d205773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204198, d205773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203955 q = 0) : d205600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203955, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203955, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204199 q = 0) : d205774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204199, d205774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204199, d205774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204200 q = 0) : d205775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204200, d205775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204200, d205775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204206 q = 0) : d205781 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204206, d205781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204206, d205781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204207 q = 0) : d205782 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204207, d205782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204207, d205782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19649 (p : Pattern) (selected : d204213 p = 0) : d205788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204188 q = 0) : d205763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204188, d205763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19644 q selected
    | true =>
      simp only [d204188, d205763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19645 q selected
  have h2 (q : Pattern) (selected : d204189 q = 0) : d205764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204189, d205764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204189, d205764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204190 q = 0) : d205765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204190, d205765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204190, d205765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204193 q = 0) : d205768 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204193, d205768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19645 q selected
    | true =>
      simp only [d204193, d205768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19646 q selected
  have h5 (q : Pattern) (selected : d204194 q = 0) : d205769 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204194, d205769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204194, d205769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204195 q = 0) : d205770 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204195, d205770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204195, d205770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204196 q = 0) : d205771 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204196, d205771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204196, d205771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204203 q = 0) : d205778 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204203, d205778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19645 q selected
    | true =>
      simp only [d204203, d205778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19647 q selected
  have h9 (q : Pattern) (selected : d204204 q = 0) : d205779 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204204, d205779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204204, d205779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204205 q = 0) : d205780 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204205, d205780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204205, d205780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204208 q = 0) : d205783 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204208, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19647 q selected
    | true =>
      simp only [d204208, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19648 q selected
  have h12 (q : Pattern) (selected : d204209 q = 0) : d205784 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204209, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204209, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d204210 q = 0) : d205785 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204210, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204210, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204211 q = 0) : d205786 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204211, d205786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d204211, d205786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d204212 q = 0) : d205787 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d204212, d205787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204212, d205787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d204213 q = 0) : d205788 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d204213, d205788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d204213, d205788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro19650 (p : Pattern) (selected : d204218 p = 0) : d205793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204203 q = 0) : d205778 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204203, d205778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19645 q selected
    | true =>
      simp only [d204203, d205778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19647 q selected
  have h2 (q : Pattern) (selected : d204204 q = 0) : d205779 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204204, d205779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204204, d205779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204205 q = 0) : d205780 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204205, d205780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204205, d205780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204208 q = 0) : d205783 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204208, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19647 q selected
    | true =>
      simp only [d204208, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19648 q selected
  have h5 (q : Pattern) (selected : d204209 q = 0) : d205784 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204209, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204209, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204210 q = 0) : d205785 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204210, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204210, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204211 q = 0) : d205786 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204211, d205786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204211, d205786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204216 q = 0) : d205791 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204216, d205791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204216, d205791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204217 q = 0) : d205792 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d204217, d205792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204217, d205792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204218 q = 0) : d205793 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d204218, d205793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204218, d205793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19651 (p : Pattern) (selected : d204224 p = 0) : d205799 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204214 q = 0) : d205789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204214, d205789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19649 q selected
    | true =>
      simp only [d204214, d205789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204215 q = 0) : d205790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204215, d205790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204215, d205790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204219 q = 0) : d205794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204219, d205794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19650 q selected
    | true =>
      simp only [d204219, d205794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204220 q = 0) : d205795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204220, d205795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204220, d205795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204221 q = 0) : d205796 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204221, d205796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204221, d205796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204222 q = 0) : d205797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204222, d205797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204222, d205797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204223 q = 0) : d205798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204223, d205798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204223, d205798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204224 q = 0) : d205799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204224, d205799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204224, d205799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19652 (p : Pattern) (selected : d204226 p = 0) : d205801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204208 q = 0) : d205783 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204208, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19647 q selected
    | true =>
      simp only [d204208, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19648 q selected
  have h2 (q : Pattern) (selected : d204209 q = 0) : d205784 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204209, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204209, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204210 q = 0) : d205785 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204210, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204210, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204216 q = 0) : d205791 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204216, d205791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204216, d205791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204225 q = 0) : d205800 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d204225, d205800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204225, d205800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204226 q = 0) : d205801 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d204226, d205801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204226, d205801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19653 (p : Pattern) (selected : d204232 p = 0) : d205807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204219 q = 0) : d205794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204219, d205794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19650 q selected
    | true =>
      simp only [d204219, d205794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204220 q = 0) : d205795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204220, d205795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204220, d205795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204227 q = 0) : d205802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204227, d205802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19652 q selected
    | true =>
      simp only [d204227, d205802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204228 q = 0) : d205803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204228, d205803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204228, d205803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204229 q = 0) : d205804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204229, d205804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204229, d205804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204230 q = 0) : d205805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204230, d205805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204230, d205805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204231 q = 0) : d205806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204231, d205806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204231, d205806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204232 q = 0) : d205807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204232, d205807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204232, d205807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19654 (p : Pattern) (selected : d204248 p = 0) : d205762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204234 q = 0) : d205746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204234, d205746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204234, d205746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19614 q selected
  have h2 (q : Pattern) (selected : d204048 q = 0) : d205572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204048, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19614 q selected
    | true =>
      simp only [d204048, d205572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204235 q = 0) : d205747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204235, d205747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204235, d205747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204049 q = 0) : d205573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204049, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204049, d205573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204236 q = 0) : d205748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204236, d205748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204236, d205748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204237 q = 0) : d205749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204237, d205749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204237, d205749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204238 q = 0) : d205751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204238, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204238, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19618 q selected
  have h8 (q : Pattern) (selected : d204058 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204058, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19618 q selected
    | true =>
      simp only [d204058, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204239 q = 0) : d205752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204239, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204239, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204059 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204059, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d204059, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d204240 q = 0) : d205753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204240, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204240, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d204241 q = 0) : d205754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204241, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d204241, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d204242 q = 0) : d205755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204242, d205755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204242, d205755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204243 q = 0) : d205757 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204243, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204243, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19619 q selected
  have h15 (q : Pattern) (selected : d204064 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204064, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19619 q selected
    | true =>
      simp only [d204064, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d204244 q = 0) : d205758 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204244, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d204244, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d204065 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204065, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d204065, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d204245 q = 0) : d205759 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204245, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d204245, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d204246 q = 0) : d205760 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204246, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d204246, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d204247 q = 0) : d205761 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204247, d205761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d204247, d205761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d204248 q = 0) : d205762 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204248, d205762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d204248, d205762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro19655 (p : Pattern) (selected : d204255 p = 0) : d205777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204238 q = 0) : d205751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204238, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204238, d205751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19618 q selected
  have h2 (q : Pattern) (selected : d204058 q = 0) : d205582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204058, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19618 q selected
    | true =>
      simp only [d204058, d205582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204239 q = 0) : d205752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204239, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204239, d205752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204059 q = 0) : d205583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204059, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204059, d205583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204240 q = 0) : d205753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204240, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204240, d205753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204241 q = 0) : d205754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204241, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204241, d205754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204249 q = 0) : d205772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204249, d205772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204249, d205772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19622 q selected
  have h8 (q : Pattern) (selected : d204075 q = 0) : d205599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204075, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19622 q selected
    | true =>
      simp only [d204075, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204250 q = 0) : d205773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204250, d205773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204250, d205773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204076 q = 0) : d205600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204076, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d204076, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d204251 q = 0) : d205774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204251, d205774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204251, d205774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d204252 q = 0) : d205775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204252, d205775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d204252, d205775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d204253 q = 0) : d205776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204253, d205776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204253, d205776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204243 q = 0) : d205757 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204243, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204243, d205757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19619 q selected
  have h15 (q : Pattern) (selected : d204064 q = 0) : d205588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204064, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19619 q selected
    | true =>
      simp only [d204064, d205588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d204244 q = 0) : d205758 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204244, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d204244, d205758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d204065 q = 0) : d205589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204065, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d204065, d205589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d204245 q = 0) : d205759 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204245, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d204245, d205759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d204246 q = 0) : d205760 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204246, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d204246, d205760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d204254 q = 0) : d205766 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204254, d205766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d204254, d205766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d204255 q = 0) : d205777 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204255, d205777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d204255, d205777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro19656 (p : Pattern) (selected : d204260 p = 0) : d205782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204249 q = 0) : d205772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204249, d205772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204249, d205772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19622 q selected
  have h2 (q : Pattern) (selected : d204075 q = 0) : d205599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d204075, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19622 q selected
    | true =>
      simp only [d204075, d205599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204250 q = 0) : d205773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204250, d205773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204250, d205773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204076 q = 0) : d205600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d204076, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204076, d205600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204251 q = 0) : d205774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d204251, d205774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204251, d205774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204252 q = 0) : d205775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d204252, d205775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204252, d205775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204259 q = 0) : d205781 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d204259, d205781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204259, d205781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204260 q = 0) : d205782 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d204260, d205782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204260, d205782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19657 (p : Pattern) (selected : d204267 p = 0) : d205793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204256 q = 0) : d205778 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204256, d205778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19654 q selected
    | true =>
      simp only [d204256, d205778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19655 q selected
  have h2 (q : Pattern) (selected : d204257 q = 0) : d205779 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204257, d205779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204257, d205779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204258 q = 0) : d205780 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204258, d205780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204258, d205780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204261 q = 0) : d205783 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204261, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19655 q selected
    | true =>
      simp only [d204261, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19656 q selected
  have h5 (q : Pattern) (selected : d204262 q = 0) : d205784 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204262, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204262, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204263 q = 0) : d205785 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204263, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204263, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204264 q = 0) : d205786 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204264, d205786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204264, d205786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204265 q = 0) : d205791 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204265, d205791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204265, d205791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d204266 q = 0) : d205792 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d204266, d205792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204266, d205792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d204267 q = 0) : d205793 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d204267, d205793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d204267, d205793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19658 (p : Pattern) (selected : d204271 p = 0) : d205801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204261 q = 0) : d205783 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d204261, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19655 q selected
    | true =>
      simp only [d204261, d205783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19656 q selected
  have h2 (q : Pattern) (selected : d204262 q = 0) : d205784 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d204262, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204262, d205784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204263 q = 0) : d205785 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d204263, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204263, d205785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204265 q = 0) : d205791 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d204265, d205791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204265, d205791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204270 q = 0) : d205800 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d204270, d205800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204270, d205800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204271 q = 0) : d205801 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d204271, d205801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204271, d205801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19659 (p : Pattern) (selected : d204277 p = 0) : d205807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204268 q = 0) : d205794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204268, d205794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19657 q selected
    | true =>
      simp only [d204268, d205794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204269 q = 0) : d205795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204269, d205795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204269, d205795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204272 q = 0) : d205802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204272, d205802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19658 q selected
    | true =>
      simp only [d204272, d205802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204273 q = 0) : d205803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204273, d205803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204273, d205803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204274 q = 0) : d205804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204274, d205804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204274, d205804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204275 q = 0) : d205805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204275, d205805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204275, d205805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204276 q = 0) : d205806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204276, d205806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204276, d205806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204277 q = 0) : d205807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204277, d205807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204277, d205807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19660 (p : Pattern) (selected : d204281 p = 0) : d205812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204272 q = 0) : d205802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204272, d205802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19658 q selected
    | true =>
      simp only [d204272, d205802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204273 q = 0) : d205803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204273, d205803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204273, d205803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204278 q = 0) : d205809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204278, d205809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204278, d205809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204279 q = 0) : d205810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204279, d205810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204279, d205810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204280 q = 0) : d205811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204280, d205811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204280, d205811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204281 q = 0) : d205812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204281, d205812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204281, d205812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19661 (p : Pattern) (selected : d204287 p = 0) : d205818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204219 q = 0) : d205794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204219, d205794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19650 q selected
    | true =>
      simp only [d204219, d205794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204220 q = 0) : d205795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204220, d205795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204220, d205795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204284 q = 0) : d205815 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204284, d205815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204284, d205815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204285 q = 0) : d205816 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204285, d205816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204285, d205816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204286 q = 0) : d205817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204286, d205817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204286, d205817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204287 q = 0) : d205818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204287, d205818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204287, d205818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19662 (p : Pattern) (selected : d204293 p = 0) : d205824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204233 q = 0) : d205808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204233, d205808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19651 q selected
    | true =>
      simp only [d204233, d205808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19653 q selected
  have h2 (q : Pattern) (selected : d204282 q = 0) : d205813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204282, d205813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19659 q selected
    | true =>
      simp only [d204282, d205813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19660 q selected
  have h3 (q : Pattern) (selected : d204283 q = 0) : d205814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204283, d205814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204283, d205814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204288 q = 0) : d205819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204288, d205819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19661 q selected
    | true =>
      simp only [d204288, d205819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204289 q = 0) : d205820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204289, d205820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204289, d205820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204290 q = 0) : d205821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204290, d205821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204290, d205821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d204291 q = 0) : d205822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204291, d205822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204291, d205822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204292 q = 0) : d205823 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204292, d205823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204292, d205823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d204293 q = 0) : d205824 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204293, d205824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204293, d205824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19663 (p : Pattern) (selected : d204298 p = 0) : d205812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204227 q = 0) : d205802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d204227, d205802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19652 q selected
    | true =>
      simp only [d204227, d205802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204228 q = 0) : d205803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d204228, d205803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204228, d205803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204295 q = 0) : d205809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d204295, d205809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204295, d205809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204296 q = 0) : d205810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d204296, d205810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204296, d205810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204297 q = 0) : d205811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d204297, d205811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204297, d205811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204298 q = 0) : d205812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d204298, d205812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204298, d205812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19664 (p : Pattern) (selected : d204304 p = 0) : d205831 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204299 q = 0) : d205826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204299, d205826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19663 q selected
    | true =>
      simp only [d204299, d205826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204300 q = 0) : d205827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204300, d205827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204300, d205827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204301 q = 0) : d205828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204301, d205828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204301, d205828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204302 q = 0) : d205829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204302, d205829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204302, d205829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204303 q = 0) : d205830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204303, d205830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204303, d205830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204304 q = 0) : d205831 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204304, d205831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204304, d205831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19665 (p : Pattern) (selected : d204310 p = 0) : d205837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d203993 q = 0) : d205638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203993, d205638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203993, d205638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19599 q selected
  have h2 (q : Pattern) (selected : d203994 q = 0) : d205639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d203994, d205639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203994, d205639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204003 q = 0) : d205648 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204003, d205648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19599 q selected
    | true =>
      simp only [d204003, d205648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19602 q selected
  have h4 (q : Pattern) (selected : d204004 q = 0) : d205649 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204004, d205649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204004, d205649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204005 q = 0) : d205650 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204005, d205650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204005, d205650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204144 q = 0) : d205719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204144, d205719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19630 q selected
    | true =>
      simp only [d204144, d205719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19639 q selected
  have h7 (q : Pattern) (selected : d204157 q = 0) : d205732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204157, d205732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19640 q selected
    | true =>
      simp only [d204157, d205732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19641 q selected
  have h8 (q : Pattern) (selected : d204158 q = 0) : d205733 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204158, d205733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d204158, d205733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d204159 q = 0) : d205734 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204159, d205734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d204159, d205734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d204160 q = 0) : d205735 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204160, d205735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204160, d205735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204164 q = 0) : d205739 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204164, d205739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204164, d205739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19642 q selected
  have h12 (q : Pattern) (selected : d204166 q = 0) : d205741 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204166, d205741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204166, d205741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19643 q selected
  have h13 (q : Pattern) (selected : d204167 q = 0) : d205742 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204167, d205742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d204167, d205742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204168 q = 0) : d205743 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204168, d205743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d204168, d205743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d204169 q = 0) : d205744 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204169, d205744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d204169, d205744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d204170 q = 0) : d205745 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d204170, d205745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d204170, d205745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d204294 q = 0) : d205825 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204294, d205825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204294, d205825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19662 q selected
  have h18 (q : Pattern) (selected : d204305 q = 0) : d205832 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204305, d205832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204305, d205832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19664 q selected
  have h19 (q : Pattern) (selected : d204306 q = 0) : d205833 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204306, d205833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d204306, d205833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d204307 q = 0) : d205834 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204307, d205834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d204307, d205834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d204308 q = 0) : d205835 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204308, d205835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d204308, d205835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d204309 q = 0) : d205836 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d204309, d205836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d204309, d205836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d204310 q = 0) : d205837 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d204310, d205837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d204310, d205837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro19666 (p : Pattern) (selected : d204316 p = 0) : d205843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204311 q = 0) : d205838 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d204311, d205838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204311, d205838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19665 q selected
  have h2 (q : Pattern) (selected : d204312 q = 0) : d205839 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d204312, d205839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204312, d205839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204313 q = 0) : d205840 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d204313, d205840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204313, d205840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d204314 q = 0) : d205841 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d204314, d205841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204314, d205841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204315 q = 0) : d205842 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d204315, d205842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204315, d205842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d204316 q = 0) : d205843 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d204316, d205843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d204316, d205843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19667 (p : Pattern) (selected : d204322 p = 0) : d205849 p = 1 := by
  have h0 (q : Pattern) (selected : d202759 q = 0) : d204726 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202759, d204726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19316 q selected
    | true =>
      simp only [d202759, d204726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19353 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d203062 q = 0) : d204953 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d203062, d204953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203062, d204953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19414 q selected
  have h3 (q : Pattern) (selected : d203063 q = 0) : d204954 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d203063, d204954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203063, d204954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203486 q = 0) : d205257 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d203486, d205257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203486, d205257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19494 q selected
  have h5 (q : Pattern) (selected : d203487 q = 0) : d205258 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d203487, d205258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203487, d205258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203488 q = 0) : d205259 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d203488, d205259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203488, d205259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203917 q = 0) : d205562 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d203917, d205562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203917, d205562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19580 q selected
  have h8 (q : Pattern) (selected : d203918 q = 0) : d205563 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d203918, d205563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203918, d205563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203919 q = 0) : d205564 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d203919, d205564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203919, d205564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203920 q = 0) : d205565 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d203920, d205565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203920, d205565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d204317 q = 0) : d205844 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d204317, d205844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204317, d205844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19666 q selected
  have h12 (q : Pattern) (selected : d204318 q = 0) : d205845 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d204318, d205845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204318, d205845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d204319 q = 0) : d205846 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d204319, d205846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204319, d205846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d204320 q = 0) : d205847 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d204320, d205847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204320, d205847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d204321 q = 0) : d205848 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d204321, d205848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d204321, d205848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d204322 q = 0) : d205849 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d204322, d205849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d204322, d205849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro19668 (p : Pattern) (selected : d204328 p = 0) : d205855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204323 q = 0) : d205850 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d204323, d205850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19667 q selected
    | true =>
      simp only [d204323, d205850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204324 q = 0) : d205851 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d204324, d205851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204324, d205851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204325 q = 0) : d205852 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d204325, d205852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204325, d205852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204326 q = 0) : d205853 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d204326, d205853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204326, d205853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204327 q = 0) : d205854 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d204327, d205854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204327, d205854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204328 q = 0) : d205855 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d204328, d205855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204328, d205855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19669 (p : Pattern) (selected : d204334 p = 0) : d205861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204329 q = 0) : d205856 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d204329, d205856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19668 q selected
    | true =>
      simp only [d204329, d205856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204330 q = 0) : d205857 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d204330, d205857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204330, d205857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204331 q = 0) : d205858 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d204331, d205858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204331, d205858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204332 q = 0) : d205859 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d204332, d205859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204332, d205859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204333 q = 0) : d205860 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d204333, d205860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204333, d205860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204334 q = 0) : d205861 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d204334, d205861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204334, d205861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19670 (p : Pattern) (selected : d204340 p = 0) : d205867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204335 q = 0) : d205862 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d204335, d205862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19669 q selected
    | true =>
      simp only [d204335, d205862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204336 q = 0) : d205863 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d204336, d205863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204336, d205863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204337 q = 0) : d205864 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d204337, d205864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204337, d205864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204338 q = 0) : d205865 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d204338, d205865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204338, d205865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204339 q = 0) : d205866 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d204339, d205866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204339, d205866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204340 q = 0) : d205867 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d204340, d205867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204340, d205867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19671 (p : Pattern) (selected : d204346 p = 0) : d205873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204341 q = 0) : d205868 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d204341, d205868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19670 q selected
    | true =>
      simp only [d204341, d205868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204342 q = 0) : d205869 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d204342, d205869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204342, d205869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204343 q = 0) : d205870 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d204343, d205870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204343, d205870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204344 q = 0) : d205871 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d204344, d205871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204344, d205871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204345 q = 0) : d205872 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d204345, d205872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204345, d205872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204346 q = 0) : d205873 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d204346, d205873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204346, d205873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19672 (p : Pattern) (selected : d204352 p = 0) : d205879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204347 q = 0) : d205874 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d204347, d205874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19671 q selected
    | true =>
      simp only [d204347, d205874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204348 q = 0) : d205875 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d204348, d205875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204348, d205875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204349 q = 0) : d205876 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d204349, d205876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204349, d205876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204350 q = 0) : d205877 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d204350, d205877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204350, d205877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204351 q = 0) : d205878 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d204351, d205878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204351, d205878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204352 q = 0) : d205879 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d204352, d205879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204352, d205879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19673 (p : Pattern) (selected : d204358 p = 0) : d205885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204353 q = 0) : d205880 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d204353, d205880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19672 q selected
    | true =>
      simp only [d204353, d205880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204354 q = 0) : d205881 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d204354, d205881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204354, d205881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204355 q = 0) : d205882 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d204355, d205882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204355, d205882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204356 q = 0) : d205883 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d204356, d205883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204356, d205883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204357 q = 0) : d205884 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d204357, d205884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204357, d205884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204358 q = 0) : d205885 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d204358, d205885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204358, d205885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19674 (p : Pattern) (selected : d204364 p = 0) : d205891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204359 q = 0) : d205886 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d204359, d205886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19673 q selected
    | true =>
      simp only [d204359, d205886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d204360 q = 0) : d205887 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d204360, d205887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d204360, d205887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d204361 q = 0) : d205888 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d204361, d205888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d204361, d205888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d204362 q = 0) : d205889 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d204362, d205889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204362, d205889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204363 q = 0) : d205890 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d204363, d205890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d204363, d205890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204364 q = 0) : d205891 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d204364, d205891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204364, d205891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19675 (p : Pattern) (selected : d162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d161 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d162 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro19676 (p : Pattern) (selected : d202444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202444 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d202444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro19677 (p : Pattern) (selected : d202450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
    | true =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202449 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202450 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d202450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19678 (p : Pattern) (selected : d202456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202451 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19677 q selected
    | true =>
      simp only [d202451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202452 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202453 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202454 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202455 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d202455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202456 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d202456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19679 (p : Pattern) (selected : d202462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19678 q selected
    | true =>
      simp only [d202457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19680 (p : Pattern) (selected : d202468 p = 1) : d207675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202409 q = 1) : d202409 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202415 q = 1) : d202415 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d202439 q = 1) : d202439 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d202463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19679 q selected
    | true =>
      simp only [d202463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202464 q = 1) : d207671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202464, d207671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202464, d207671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202332 q = 1) : d202332 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d202465 q = 1) : d207672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202465, d207672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202465, d207672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202466 q = 1) : d207673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202466, d207673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202466, d207673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d202467 q = 1) : d207674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202467, d207674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202467, d207674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202468 q = 1) : d207675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202468, d207675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202468, d207675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro19681 (p : Pattern) (selected : d202480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19678 q selected
    | true =>
      simp only [d202457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202480 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19682 (p : Pattern) (selected : d202486 p = 1) : d207680 p = 1 := by
  have h0 (q : Pattern) (selected : d202409 q = 1) : d202409 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202415 q = 1) : d202415 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202439 q = 1) : d202439 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d202463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19679 q selected
    | true =>
      simp only [d202463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202464 q = 1) : d207671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202464, d207671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202464, d207671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202332 q = 1) : d202332 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d202465 q = 1) : d207672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202465, d207672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202465, d207672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202466 q = 1) : d207673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202466, d207673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202466, d207673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d202467 q = 1) : d207674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202467, d207674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202467, d207674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202473 q = 1) : d202473 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d202477 q = 1) : d202477 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d202479 q = 1) : d202479 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d202481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19681 q selected
    | true =>
      simp only [d202481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d202482 q = 1) : d207676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202482, d207676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d202482, d207676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d202339 q = 1) : d202339 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d202483 q = 1) : d207677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202483, d207677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d202483, d207677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d202484 q = 1) : d207678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202484, d207678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d202484, d207678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d202485 q = 1) : d207679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202485, d207679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d202485, d207679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d202486 q = 1) : d207680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202486, d207680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202486, d207680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro19683 (p : Pattern) (selected : d202495 p = 1) : d207687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202479 q = 1) : d202479 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19681 q selected
    | true =>
      simp only [d202481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202482 q = 1) : d207676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202482, d207676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202482, d207676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202339 q = 1) : d202339 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d202483 q = 1) : d207677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202483, d207677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202483, d207677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202493 q = 1) : d207685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202493, d207685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202493, d207685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202494 q = 1) : d207686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202494, d207686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202494, d207686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202495 q = 1) : d207687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202495, d207687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202495, d207687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19684 (p : Pattern) (selected : d202525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202520 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
  have h2 (q : Pattern) (selected : d202445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
    | true =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202521 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202522 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202523 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202524 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202525 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d202525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19685 (p : Pattern) (selected : d202531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202526 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19684 q selected
    | true =>
      simp only [d202526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202527 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202528 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202529 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202530 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d202530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202531 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d202531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19686 (p : Pattern) (selected : d202537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202532 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19685 q selected
    | true =>
      simp only [d202532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202533 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202534 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202535 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202536 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202537 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19687 (p : Pattern) (selected : d202543 p = 1) : d207697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202519 q = 1) : d202519 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202538 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19686 q selected
    | true =>
      simp only [d202538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202539 q = 1) : d207693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202539, d207693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202539, d207693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202373 q = 1) : d202373 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d202540 q = 1) : d207694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202540, d207694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202540, d207694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202541 q = 1) : d207695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202541, d207695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202541, d207695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202542 q = 1) : d207696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202542, d207696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202542, d207696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202543 q = 1) : d207697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202543, d207697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202543, d207697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19688 (p : Pattern) (selected : d202549 p = 1) : d207703 p = 1 := by
  have h0 (q : Pattern) (selected : d202403 q = 1) : d202403 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202487 q = 1) : d207681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202487, d207681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19680 q selected
    | true =>
      simp only [d202487, d207681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19682 q selected
  have h2 (q : Pattern) (selected : d202489 q = 1) : d202489 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d202490 q = 1) : d207682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202490, d207682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202490, d207682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d202491 q = 1) : d207683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202491, d207683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202491, d207683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202492 q = 1) : d207684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202492, d207684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202492, d207684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202496 q = 1) : d207688 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202496, d207688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202496, d207688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19683 q selected
  have h8 (q : Pattern) (selected : d202497 q = 1) : d207689 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202497, d207689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202497, d207689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d202498 q = 1) : d207690 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202498, d207690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d202498, d207690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d202499 q = 1) : d207691 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202499, d207691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202499, d207691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d202500 q = 1) : d207692 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202500, d207692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202500, d207692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d202544 q = 1) : d207698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202544, d207698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202544, d207698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19687 q selected
  have h13 (q : Pattern) (selected : d202545 q = 1) : d207699 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202545, d207699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d202545, d207699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d202546 q = 1) : d207700 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202546, d207700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d202546, d207700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d202547 q = 1) : d207701 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202547, d207701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d202547, d207701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d202548 q = 1) : d207702 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202548, d207702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d202548, d207702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d202549 q = 1) : d207703 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202549, d207703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d202549, d207703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro19689 (p : Pattern) (selected : d202555 p = 1) : d207709 p = 1 := by
  have h0 (q : Pattern) (selected : d202388 q = 1) : d202388 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202550 q = 1) : d207704 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202550, d207704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202550, d207704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19688 q selected
  have h3 (q : Pattern) (selected : d202551 q = 1) : d207705 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202551, d207705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202551, d207705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202552 q = 1) : d207706 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202552, d207706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202552, d207706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202553 q = 1) : d207707 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202553, d207707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202553, d207707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202554 q = 1) : d207708 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202554, d207708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202554, d207708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202555 q = 1) : d207709 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202555, d207709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202555, d207709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro19690 (p : Pattern) (selected : d342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d340 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d341 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d161 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d342 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro19691 (p : Pattern) (selected : d202619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202615 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202616 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202617 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202618 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202619 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d202619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19692 (p : Pattern) (selected : d202625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202620 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19691 q selected
    | true =>
      simp only [d202620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202621 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202622 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202623 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
    | true =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202624 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202449 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d202449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d202625 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d202625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19693 (p : Pattern) (selected : d202631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19692 q selected
    | true =>
      simp only [d202626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19677 q selected
  have h2 (q : Pattern) (selected : d202627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202451 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19677 q selected
    | true =>
      simp only [d202451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202452 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202453 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202454 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202630 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d202630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202631 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d202631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19694 (p : Pattern) (selected : d202637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19693 q selected
    | true =>
      simp only [d202632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19678 q selected
    | true =>
      simp only [d202457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19695 (p : Pattern) (selected : d202649 p = 1) : d207714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202576 q = 1) : d202576 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202582 q = 1) : d202582 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d202614 q = 1) : d202614 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d202638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19694 q selected
    | true =>
      simp only [d202638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19679 q selected
  have h5 (q : Pattern) (selected : d202639 q = 1) : d207710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202639, d207710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202639, d207710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202645 q = 1) : d202645 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d202646 q = 1) : d207711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202646, d207711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202646, d207711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202647 q = 1) : d207712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202647, d207712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202647, d207712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d202648 q = 1) : d207713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202648, d207713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202648, d207713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202649 q = 1) : d207714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202649, d207714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202649, d207714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro19696 (p : Pattern) (selected : d202661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19693 q selected
    | true =>
      simp only [d202632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19678 q selected
    | true =>
      simp only [d202457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202661 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19697 (p : Pattern) (selected : d202670 p = 1) : d207719 p = 1 := by
  have h0 (q : Pattern) (selected : d202576 q = 1) : d202576 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202582 q = 1) : d202582 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202614 q = 1) : d202614 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d202638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19694 q selected
    | true =>
      simp only [d202638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19679 q selected
  have h4 (q : Pattern) (selected : d202639 q = 1) : d207710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202639, d207710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202639, d207710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202645 q = 1) : d202645 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d202646 q = 1) : d207711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202646, d207711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202646, d207711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202647 q = 1) : d207712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202647, d207712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202647, d207712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202648 q = 1) : d207713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202648, d207713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202648, d207713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d202654 q = 1) : d202654 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d202658 q = 1) : d202658 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d202660 q = 1) : d202660 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d202662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19696 q selected
    | true =>
      simp only [d202662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19681 q selected
  have h13 (q : Pattern) (selected : d202663 q = 1) : d207715 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202663, d207715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d202663, d207715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d202666 q = 1) : d202666 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d202667 q = 1) : d207716 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202667, d207716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d202667, d207716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d202668 q = 1) : d207717 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202668, d207717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d202668, d207717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d202669 q = 1) : d207718 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202669, d207718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202669, d207718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d202670 q = 1) : d207719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202670, d207719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d202670, d207719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro19698 (p : Pattern) (selected : d202679 p = 1) : d207726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202660 q = 1) : d202660 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19696 q selected
    | true =>
      simp only [d202662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19681 q selected
  have h3 (q : Pattern) (selected : d202663 q = 1) : d207715 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202663, d207715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202663, d207715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202666 q = 1) : d202666 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d202667 q = 1) : d207716 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202667, d207716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202667, d207716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202677 q = 1) : d207724 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202677, d207724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202677, d207724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202678 q = 1) : d207725 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202678, d207725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202678, d207725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202679 q = 1) : d207726 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202679, d207726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202679, d207726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19699 (p : Pattern) (selected : d202716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202711 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19691 q selected
  have h2 (q : Pattern) (selected : d202620 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19691 q selected
    | true =>
      simp only [d202620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202712 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202621 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202713 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202714 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202520 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
  have h8 (q : Pattern) (selected : d202445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
    | true =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202521 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d202522 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d202523 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d202523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d202715 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d202524 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d202524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d202716 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d202716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d202716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19700 (p : Pattern) (selected : d202722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202717 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19699 q selected
    | true =>
      simp only [d202717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19684 q selected
  have h2 (q : Pattern) (selected : d202718 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202719 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202526 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19684 q selected
    | true =>
      simp only [d202526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202527 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202528 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202720 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202529 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202721 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d202721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202722 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d202722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19701 (p : Pattern) (selected : d202728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19700 q selected
    | true =>
      simp only [d202723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202724 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202532 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19685 q selected
    | true =>
      simp only [d202532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202533 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202725 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202726 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202727 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202728 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19702 (p : Pattern) (selected : d202740 p = 1) : d207736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202710 q = 1) : d202710 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202729 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19701 q selected
    | true =>
      simp only [d202729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19686 q selected
  have h3 (q : Pattern) (selected : d202730 q = 1) : d207732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202730, d207732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202730, d207732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202736 q = 1) : d202736 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d202737 q = 1) : d207733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202737, d207733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202737, d207733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202738 q = 1) : d207734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202738, d207734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202738, d207734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202739 q = 1) : d207735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202739, d207735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202739, d207735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202740 q = 1) : d207736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202740, d207736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202740, d207736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19703 (p : Pattern) (selected : d202752 p = 1) : d207742 p = 1 := by
  have h0 (q : Pattern) (selected : d202570 q = 1) : d202570 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202671 q = 1) : d207720 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202671, d207720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19695 q selected
    | true =>
      simp only [d202671, d207720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19697 q selected
  have h2 (q : Pattern) (selected : d202673 q = 1) : d202673 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d202674 q = 1) : d207721 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202674, d207721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202674, d207721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d202675 q = 1) : d207722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202675, d207722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202675, d207722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202676 q = 1) : d207723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202676, d207723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202676, d207723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202680 q = 1) : d207727 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202680, d207727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202680, d207727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19698 q selected
  have h8 (q : Pattern) (selected : d202682 q = 1) : d202682 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d202683 q = 1) : d207728 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202683, d207728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202683, d207728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202684 q = 1) : d207729 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202684, d207729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202684, d207729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d202685 q = 1) : d207730 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202685, d207730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d202685, d207730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d202686 q = 1) : d207731 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202686, d207731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202686, d207731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d202741 q = 1) : d207737 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202741, d207737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202741, d207737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19702 q selected
  have h14 (q : Pattern) (selected : d202747 q = 1) : d202747 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d202748 q = 1) : d207738 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202748, d207738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d202748, d207738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d202749 q = 1) : d207739 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202749, d207739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d202749, d207739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d202750 q = 1) : d207740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202750, d207740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d202750, d207740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d202751 q = 1) : d207741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202751, d207741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d202751, d207741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d202752 q = 1) : d207742 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202752, d207742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d202752, d207742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro19704 (p : Pattern) (selected : d202758 p = 1) : d207748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202753 q = 1) : d207743 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202753, d207743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202753, d207743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19703 q selected
  have h2 (q : Pattern) (selected : d202754 q = 1) : d207744 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202754, d207744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202754, d207744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202755 q = 1) : d207745 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202755, d207745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202755, d207745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202756 q = 1) : d207746 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202756, d207746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202756, d207746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202757 q = 1) : d207747 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202757, d207747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202757, d207747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202758 q = 1) : d207748 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202758, d207748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202758, d207748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19705 (p : Pattern) (selected : d566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d340 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d565 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d341 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d566 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro19706 (p : Pattern) (selected : d202857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202851 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19705 q selected
    | true =>
      simp only [d202851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202852 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202615 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202616 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202853 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202854 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202855 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202856 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202857 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d202857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19707 (p : Pattern) (selected : d202863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202615 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202616 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202855 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202856 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202863 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d202863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19708 (p : Pattern) (selected : d202869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202858 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19706 q selected
    | true =>
      simp only [d202858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202859 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202860 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202861 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202620 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19691 q selected
    | true =>
      simp only [d202620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202621 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202622 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202623 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202862 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
    | true =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d202865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d202866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d202867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d202867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d202445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
    | true =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d202446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d202447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d202448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d202448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d202868 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d202868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d202869 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d202869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro19709 (p : Pattern) (selected : d202876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202870 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19708 q selected
    | true =>
      simp only [d202870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19692 q selected
  have h2 (q : Pattern) (selected : d202871 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202872 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19692 q selected
    | true =>
      simp only [d202626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19677 q selected
  have h5 (q : Pattern) (selected : d202627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202873 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202874 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202875 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d202875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202876 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d202876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19710 (p : Pattern) (selected : d202880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19692 q selected
    | true =>
      simp only [d202626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19677 q selected
  have h2 (q : Pattern) (selected : d202627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202874 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d202874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202879 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d202879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202880 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d202880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19711 (p : Pattern) (selected : d202886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19709 q selected
    | true =>
      simp only [d202877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19710 q selected
    | true =>
      simp only [d202881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19712 (p : Pattern) (selected : d202890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19710 q selected
    | true =>
      simp only [d202881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202887 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202890 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19713 (p : Pattern) (selected : d202902 p = 1) : d207754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202803 q = 1) : d202803 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202812 q = 1) : d202812 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d202850 q = 1) : d202850 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d202891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19711 q selected
    | true =>
      simp only [d202891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19712 q selected
  have h5 (q : Pattern) (selected : d202892 q = 1) : d207750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202892, d207750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202892, d207750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202898 q = 1) : d202898 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d202899 q = 1) : d207751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202899, d207751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202899, d207751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202900 q = 1) : d207752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202900, d207752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202900, d207752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d202901 q = 1) : d207753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202901, d207753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202901, d207753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202902 q = 1) : d207754 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202902, d207754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202902, d207754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro19714 (p : Pattern) (selected : d202916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19709 q selected
    | true =>
      simp only [d202877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19710 q selected
    | true =>
      simp only [d202881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19715 (p : Pattern) (selected : d202917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d202881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19710 q selected
    | true =>
      simp only [d202881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d202882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202887 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d202887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d202888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d202888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d202889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202917 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d202917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19716 (p : Pattern) (selected : d202926 p = 1) : d207759 p = 1 := by
  have h0 (q : Pattern) (selected : d202803 q = 1) : d202803 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202812 q = 1) : d202812 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202850 q = 1) : d202850 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d202891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19711 q selected
    | true =>
      simp only [d202891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19712 q selected
  have h4 (q : Pattern) (selected : d202892 q = 1) : d207750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202892, d207750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202892, d207750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d202898 q = 1) : d202898 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d202899 q = 1) : d207751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202899, d207751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202899, d207751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202900 q = 1) : d207752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202900, d207752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202900, d207752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202901 q = 1) : d207753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202901, d207753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202901, d207753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d202908 q = 1) : d202908 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d202913 q = 1) : d202913 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d202915 q = 1) : d202915 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d202918 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19714 q selected
    | true =>
      simp only [d202918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19715 q selected
  have h13 (q : Pattern) (selected : d202919 q = 1) : d207755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202919, d207755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d202919, d207755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d202922 q = 1) : d202922 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d202923 q = 1) : d207756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202923, d207756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d202923, d207756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d202924 q = 1) : d207757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202924, d207757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d202924, d207757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d202925 q = 1) : d207758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202925, d207758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202925, d207758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d202926 q = 1) : d207759 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202926, d207759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d202926, d207759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro19717 (p : Pattern) (selected : d202946 p = 1) : d207766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202915 q = 1) : d202915 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d202918 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d202918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19714 q selected
    | true =>
      simp only [d202918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19715 q selected
  have h3 (q : Pattern) (selected : d202919 q = 1) : d207755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202919, d207755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202919, d207755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202922 q = 1) : d202922 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d202923 q = 1) : d207756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202923, d207756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202923, d207756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202944 q = 1) : d207764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202944, d207764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202944, d207764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202945 q = 1) : d207765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202945, d207765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202945, d207765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202946 q = 1) : d207766 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202946, d207766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202946, d207766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19718 (p : Pattern) (selected : d203005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202995 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19706 q selected
  have h2 (q : Pattern) (selected : d202858 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19706 q selected
    | true =>
      simp only [d202858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d202996 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202859 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d202859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202997 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202998 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202711 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19691 q selected
  have h8 (q : Pattern) (selected : d202620 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19691 q selected
    | true =>
      simp only [d202620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202712 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202621 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d202621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d202713 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d202714 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d202714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d202999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d202999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
  have h15 (q : Pattern) (selected : d202864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
    | true =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d202865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203002 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203003 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d203003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d202520 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
  have h21 (q : Pattern) (selected : d202445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19676 q selected
    | true =>
      simp only [d202445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d202521 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d202521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d202446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d202522 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d202522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d202523 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d202523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d203004 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d203004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d203005 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro19719 (p : Pattern) (selected : d203012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19718 q selected
    | true =>
      simp only [d203006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19699 q selected
  have h2 (q : Pattern) (selected : d203007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d202717 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19699 q selected
    | true =>
      simp only [d202717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19684 q selected
  have h5 (q : Pattern) (selected : d202718 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202719 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203009 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203010 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203011 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203012 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19720 (p : Pattern) (selected : d203016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202717 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d202717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19699 q selected
    | true =>
      simp only [d202717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19684 q selected
  have h2 (q : Pattern) (selected : d202718 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d202718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202719 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d202719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203010 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203015 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203016 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19721 (p : Pattern) (selected : d203022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19719 q selected
    | true =>
      simp only [d203013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19720 q selected
    | true =>
      simp only [d203017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203019 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203020 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203021 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203022 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19722 (p : Pattern) (selected : d203026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19720 q selected
    | true =>
      simp only [d203017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203023 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203024 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203025 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203026 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19723 (p : Pattern) (selected : d203038 p = 1) : d207776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202994 q = 1) : d202994 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203027 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19721 q selected
    | true =>
      simp only [d203027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19722 q selected
  have h3 (q : Pattern) (selected : d203028 q = 1) : d207772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203028, d207772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203028, d207772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203034 q = 1) : d203034 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d203035 q = 1) : d207773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203035, d207773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203035, d207773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203036 q = 1) : d207774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203036, d207774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203036, d207774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203037 q = 1) : d207775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203037, d207775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203037, d207775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203038 q = 1) : d207776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203038, d207776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203038, d207776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19724 (p : Pattern) (selected : d203055 p = 1) : d207782 p = 1 := by
  have h0 (q : Pattern) (selected : d202795 q = 1) : d202795 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202927 q = 1) : d207760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202927, d207760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19713 q selected
    | true =>
      simp only [d202927, d207760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19716 q selected
  have h2 (q : Pattern) (selected : d202940 q = 1) : d202940 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d202941 q = 1) : d207761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202941, d207761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202941, d207761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d202942 q = 1) : d207762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202942, d207762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202942, d207762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d202943 q = 1) : d207763 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202943, d207763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202943, d207763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d202947 q = 1) : d207767 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202947, d207767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202947, d207767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19717 q selected
  have h8 (q : Pattern) (selected : d202949 q = 1) : d202949 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d202950 q = 1) : d207768 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202950, d207768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202950, d207768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202951 q = 1) : d207769 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202951, d207769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202951, d207769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d202952 q = 1) : d207770 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202952, d207770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d202952, d207770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d202953 q = 1) : d207771 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202953, d207771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202953, d207771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203039 q = 1) : d207777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d203039, d207777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203039, d207777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19723 q selected
  have h14 (q : Pattern) (selected : d203050 q = 1) : d203050 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d203051 q = 1) : d207778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d203051, d207778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203051, d207778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d203052 q = 1) : d207779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d203052, d207779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203052, d207779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d203053 q = 1) : d207780 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d203053, d207780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203053, d207780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d203054 q = 1) : d207781 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d203054, d207781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d203054, d207781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d203055 q = 1) : d207782 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d203055, d207782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203055, d207782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro19725 (p : Pattern) (selected : d203061 p = 1) : d207788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203056 q = 1) : d207783 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d203056, d207783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203056, d207783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19724 q selected
  have h2 (q : Pattern) (selected : d203057 q = 1) : d207784 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d203057, d207784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203057, d207784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203058 q = 1) : d207785 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d203058, d207785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203058, d207785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203059 q = 1) : d207786 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d203059, d207786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203059, d207786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203060 q = 1) : d207787 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d203060, d207787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203060, d207787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203061 q = 1) : d207788 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d203061, d207788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203061, d207788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19726 (p : Pattern) (selected : d854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d853 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d339 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d340 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d565 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d854 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro19727 (p : Pattern) (selected : d860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d340 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d565 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d859 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d860 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro19728 (p : Pattern) (selected : d1235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1233 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1234 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1235 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19729 (p : Pattern) (selected : d203211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203201 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19726 q selected
    | true =>
      simp only [d203201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203202 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203203 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19727 q selected
    | true =>
      simp only [d203203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203204 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203205 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203206 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19705 q selected
    | true =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h8 (q : Pattern) (selected : d203208 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203209 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d203210 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203211 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19730 (p : Pattern) (selected : d203222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d203207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19705 q selected
    | true =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203208 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202615 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d202616 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203216 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203217 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d203218 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
  have h8 (q : Pattern) (selected : d203219 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d203220 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d203221 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d203222 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19731 (p : Pattern) (selected : d203228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d203207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19705 q selected
    | true =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203208 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203209 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d203210 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203218 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
  have h6 (q : Pattern) (selected : d203219 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d203220 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d203221 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d203228 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro19732 (p : Pattern) (selected : d203235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d203218 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203219 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d202441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203233 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203234 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d203235 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d203235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro19733 (p : Pattern) (selected : d203241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19729 q selected
    | true =>
      simp only [d203212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203213 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203215 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203223 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19730 q selected
    | true =>
      simp only [d203223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203224 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203225 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203226 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203227 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203229 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19731 q selected
    | true =>
      simp only [d203229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203230 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d203231 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d203232 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d203236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
    | true =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203238 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203239 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203240 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203241 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro19734 (p : Pattern) (selected : d203244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203223 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19730 q selected
    | true =>
      simp only [d203223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203224 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203225 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203226 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
    | true =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203238 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203239 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203242 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203243 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203244 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro19735 (p : Pattern) (selected : d203248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
    | true =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203238 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203239 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203243 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203248 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19736 (p : Pattern) (selected : d203255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203245 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19733 q selected
    | true =>
      simp only [d203245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19734 q selected
  have h2 (q : Pattern) (selected : d203246 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203247 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203249 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19734 q selected
    | true =>
      simp only [d203249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19735 q selected
  have h5 (q : Pattern) (selected : d203250 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203251 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203252 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203253 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203254 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203255 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19737 (p : Pattern) (selected : d203259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203249 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19734 q selected
    | true =>
      simp only [d203249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19735 q selected
  have h2 (q : Pattern) (selected : d203250 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203251 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203253 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203258 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203259 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19738 (p : Pattern) (selected : d203265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203256 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19736 q selected
    | true =>
      simp only [d203256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203257 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19737 q selected
    | true =>
      simp only [d203260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203262 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203263 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203264 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203265 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19739 (p : Pattern) (selected : d203269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19737 q selected
    | true =>
      simp only [d203260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203266 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203267 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203268 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203269 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro19740 (p : Pattern) (selected : d203281 p = 1) : d207795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203153 q = 1) : d203153 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203162 q = 1) : d203162 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d203200 q = 1) : d203200 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d203270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19738 q selected
    | true =>
      simp only [d203270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19739 q selected
  have h5 (q : Pattern) (selected : d203271 q = 1) : d207791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203271, d207791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203271, d207791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203277 q = 1) : d203277 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d203278 q = 1) : d207792 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203278, d207792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203278, d207792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203279 q = 1) : d207793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203279, d207793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203279, d207793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203280 q = 1) : d207794 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203280, d207794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203280, d207794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203281 q = 1) : d207795 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203281, d207795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203281, d207795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro19741 (p : Pattern) (selected : d203295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203256 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19736 q selected
    | true =>
      simp only [d203256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203257 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19737 q selected
    | true =>
      simp only [d203260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203262 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203263 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203264 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19742 (p : Pattern) (selected : d203296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d203260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19737 q selected
    | true =>
      simp only [d203260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d203261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203266 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d203266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203267 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d203267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203268 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d203268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203296 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro19743 (p : Pattern) (selected : d203305 p = 1) : d207800 p = 1 := by
  have h0 (q : Pattern) (selected : d203153 q = 1) : d203153 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203162 q = 1) : d203162 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203200 q = 1) : d203200 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d203270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19738 q selected
    | true =>
      simp only [d203270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19739 q selected
  have h4 (q : Pattern) (selected : d203271 q = 1) : d207791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203271, d207791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203271, d207791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d203277 q = 1) : d203277 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d203278 q = 1) : d207792 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203278, d207792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203278, d207792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203279 q = 1) : d207793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203279, d207793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203279, d207793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203280 q = 1) : d207794 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203280, d207794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203280, d207794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d203287 q = 1) : d203287 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d203292 q = 1) : d203292 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d203294 q = 1) : d203294 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d203297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19741 q selected
    | true =>
      simp only [d203297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19742 q selected
  have h13 (q : Pattern) (selected : d203298 q = 1) : d207796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203298, d207796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203298, d207796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203301 q = 1) : d203301 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d203302 q = 1) : d207797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203302, d207797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203302, d207797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d203303 q = 1) : d207798 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203303, d207798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d203303, d207798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203304 q = 1) : d207799 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203304, d207799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203304, d207799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d203305 q = 1) : d207800 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203305, d207800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203305, d207800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro19744 (p : Pattern) (selected : d203325 p = 1) : d207807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203294 q = 1) : d203294 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d203297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19741 q selected
    | true =>
      simp only [d203297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19742 q selected
  have h3 (q : Pattern) (selected : d203298 q = 1) : d207796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d203298, d207796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203298, d207796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203301 q = 1) : d203301 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d203302 q = 1) : d207797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d203302, d207797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203302, d207797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203323 q = 1) : d207805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d203323, d207805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203323, d207805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203324 q = 1) : d207806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d203324, d207806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203324, d207806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203325 q = 1) : d207807 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d203325, d207807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203325, d207807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro19745 (p : Pattern) (selected : d203422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203404 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19729 q selected
  have h2 (q : Pattern) (selected : d203212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19729 q selected
    | true =>
      simp only [d203212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203405 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203213 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203406 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203407 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19730 q selected
  have h8 (q : Pattern) (selected : d203223 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19730 q selected
    | true =>
      simp only [d203223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203224 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203413 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19731 q selected
  have h15 (q : Pattern) (selected : d203229 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19731 q selected
    | true =>
      simp only [d203229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203414 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d203230 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d203230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203415 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203416 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d203416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d203417 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
  have h21 (q : Pattern) (selected : d203236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
    | true =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d203418 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d203418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d203237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d203419 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d203419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d203420 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d203420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d203421 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d203421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d203422 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro19746 (p : Pattern) (selected : d203425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19730 q selected
  have h2 (q : Pattern) (selected : d203223 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19730 q selected
    | true =>
      simp only [d203223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203224 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203417 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
  have h8 (q : Pattern) (selected : d203236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
    | true =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203418 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203419 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203420 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d203423 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203424 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d203424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d203425 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d203425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro19747 (p : Pattern) (selected : d203429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203417 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
  have h2 (q : Pattern) (selected : d203236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19732 q selected
    | true =>
      simp only [d203236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203418 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203419 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203420 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203424 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d203424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203429 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d203429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro19748 (p : Pattern) (selected : d203436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203426 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19745 q selected
    | true =>
      simp only [d203426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19746 q selected
  have h2 (q : Pattern) (selected : d203427 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203428 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203430 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19746 q selected
    | true =>
      simp only [d203430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19747 q selected
  have h5 (q : Pattern) (selected : d203431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203432 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d203433 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d203434 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d203434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d203435 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d203436 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro19749 (p : Pattern) (selected : d203440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203430 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d203430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19746 q selected
    | true =>
      simp only [d203430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19747 q selected
  have h2 (q : Pattern) (selected : d203431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d203431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203432 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d203432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d203434 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d203434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203439 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d203439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d203439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203440 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d203440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
