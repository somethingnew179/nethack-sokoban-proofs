/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalDiagram
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC0 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1 (pattern : Twelve) (guard : d3241 pattern = 1) : d0 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) ≤ (0 : Int) + 1
  decide
theorem goalC2 (pattern : Twelve) (guard : d3242 pattern = 1) : d0 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d3242, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1 pattern childGuard
    simpa only [d3242, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC3 (pattern : Twelve) (guard : d3243 pattern = 1) : d0 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC0 pattern childGuard
    simpa only [d3243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC2 pattern childGuard
    simpa only [d3243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC4 (pattern : Twelve) (guard : d3242 pattern = 1) : d26 pattern ≤ (0 : Int) + d26 pattern := by
  omega
theorem goalC5 (pattern : Twelve) (guard : d3241 pattern = 1) : d17 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d3241, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d3241, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC6 (pattern : Twelve) (guard : d1867 pattern = 1) : d1 pattern ≤ (0 : Int) + d1 pattern := by
  omega
theorem goalC7 (pattern : Twelve) (guard : d3244 pattern = 1) : d27 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC5 pattern childGuard
    simpa only [d3244, d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC6 pattern childGuard
    simpa only [d3244, d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC8 (pattern : Twelve) (guard : d3245 pattern = 1) : d50 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC4 pattern childGuard
    simpa only [d3245, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC7 pattern childGuard
    simpa only [d3245, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC9 (pattern : Twelve) (guard : d3246 pattern = 1) : d72 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3243 pattern = 1 := by simpa only [d3246, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC3 pattern childGuard
    simpa only [d3246, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3246, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC8 pattern childGuard
    simpa only [d3246, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC10 (pattern : Twelve) (guard : d3241 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem goalC11 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) ≤ (0 : Int) + 1
  decide
theorem goalC12 (pattern : Twelve) (guard : d3244 pattern = 1) : d0 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC10 pattern childGuard
    simpa only [d3244, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC11 pattern childGuard
    simpa only [d3244, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC13 (pattern : Twelve) (guard : d3245 pattern = 1) : d0 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC2 pattern childGuard
    simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC12 pattern childGuard
    simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC14 (pattern : Twelve) (guard : d1866 pattern = 1) : d8 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1866, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1847 pattern childGuard
    simpa only [d1866, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC15 (pattern : Twelve) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC16 (pattern : Twelve) (guard : d1867 pattern = 1) : d18 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC14 pattern childGuard
    simpa only [d1867, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC15 pattern childGuard
    simpa only [d1867, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC17 (pattern : Twelve) (guard : d3244 pattern = 1) : d28 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d28, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC5 pattern childGuard
    simpa only [d3244, d28, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d28, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC16 pattern childGuard
    simpa only [d3244, d28, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC18 (pattern : Twelve) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC19 (pattern : Twelve) (guard : d1867 pattern = 1) : d19 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d1867, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC18 pattern childGuard
    simpa only [d1867, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC20 (pattern : Twelve) (guard : d3247 pattern = 1) : d29 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d29, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC19 pattern childGuard
    simpa only [d3247, d29, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d29, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d3247, d29, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC21 (pattern : Twelve) (guard : d3248 pattern = 1) : d51 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC17 pattern childGuard
    simpa only [d3248, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC20 pattern childGuard
    simpa only [d3248, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC22 (pattern : Twelve) (guard : d3249 pattern = 1) : d73 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC13 pattern childGuard
    simpa only [d3249, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC21 pattern childGuard
    simpa only [d3249, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC23 (pattern : Twelve) (guard : d3250 pattern = 1) : d91 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3246 pattern = 1 := by simpa only [d3250, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC9 pattern childGuard
    simpa only [d3250, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3250, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC22 pattern childGuard
    simpa only [d3250, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC24 (pattern : Twelve) (guard : d3241 pattern = 1) : d2 pattern ≤ (0 : Int) + d3 pattern := by
  change (2 : Int) ≤ (0 : Int) + 3
  decide
theorem goalC25 (pattern : Twelve) (guard : d3242 pattern = 1) : d30 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d30, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d3242, d30, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d30, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC24 pattern childGuard
    simpa only [d3242, d30, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC26 (pattern : Twelve) (guard : d3241 pattern = 1) : d0 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem goalC27 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC28 (pattern : Twelve) (guard : d1866 pattern = 1) : d12 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1866, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC27 pattern childGuard
    simpa only [d1866, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC29 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC30 (pattern : Twelve) (guard : d1867 pattern = 1) : d20 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC28 pattern childGuard
    simpa only [d1867, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC29 pattern childGuard
    simpa only [d1867, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC31 (pattern : Twelve) (guard : d3244 pattern = 1) : d31 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d31, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC26 pattern childGuard
    simpa only [d3244, d31, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d31, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC30 pattern childGuard
    simpa only [d3244, d31, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC32 (pattern : Twelve) (guard : d3245 pattern = 1) : d52 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC25 pattern childGuard
    simpa only [d3245, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC31 pattern childGuard
    simpa only [d3245, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC33 (pattern : Twelve) (guard : d1867 pattern = 1) : d2 pattern ≤ (0 : Int) + d3 pattern := by
  change (2 : Int) ≤ (0 : Int) + 3
  decide
theorem goalC34 (pattern : Twelve) (guard : d3244 pattern = 1) : d30 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d30, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC26 pattern childGuard
    simpa only [d3244, d30, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d30, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC33 pattern childGuard
    simpa only [d3244, d30, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC35 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem goalC36 (pattern : Twelve) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC37 (pattern : Twelve) (guard : d1867 pattern = 1) : d17 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC35 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC36 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC38 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC39 (pattern : Twelve) (guard : d3247 pattern = 1) : d32 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d32, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC37 pattern childGuard
    simpa only [d3247, d32, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d32, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC38 pattern childGuard
    simpa only [d3247, d32, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC40 (pattern : Twelve) (guard : d3248 pattern = 1) : d53 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC34 pattern childGuard
    simpa only [d3248, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC39 pattern childGuard
    simpa only [d3248, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC41 (pattern : Twelve) (guard : d3249 pattern = 1) : d74 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC32 pattern childGuard
    simpa only [d3249, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC40 pattern childGuard
    simpa only [d3249, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC42 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem goalC43 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC44 (pattern : Twelve) (guard : d3247 pattern = 1) : d33 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d33, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC42 pattern childGuard
    simpa only [d3247, d33, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d33, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC43 pattern childGuard
    simpa only [d3247, d33, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC45 (pattern : Twelve) (guard : d3248 pattern = 1) : d54 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC34 pattern childGuard
    simpa only [d3248, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC44 pattern childGuard
    simpa only [d3248, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC46 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC47 (pattern : Twelve) (guard : d3247 pattern = 1) : d34 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d34, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC37 pattern childGuard
    simpa only [d3247, d34, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d34, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC46 pattern childGuard
    simpa only [d3247, d34, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC48 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC49 (pattern : Twelve) (guard : d3251 pattern = 1) : d55 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC47 pattern childGuard
    simpa only [d3251, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC48 pattern childGuard
    simpa only [d3251, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC50 (pattern : Twelve) (guard : d3252 pattern = 1) : d75 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC45 pattern childGuard
    simpa only [d3252, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC49 pattern childGuard
    simpa only [d3252, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC51 (pattern : Twelve) (guard : d3253 pattern = 1) : d92 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC41 pattern childGuard
    simpa only [d3253, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC50 pattern childGuard
    simpa only [d3253, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC52 (pattern : Twelve) (guard : d3254 pattern = 1) : d102 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d102, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC23 pattern childGuard
    simpa only [d3254, d102, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d102, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC51 pattern childGuard
    simpa only [d3254, d102, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC53 (pattern : Twelve) (guard : d3241 pattern = 1) : d0 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) ≤ (0 : Int) + 3
  decide
theorem goalC54 (pattern : Twelve) (guard : d3242 pattern = 1) : d0 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d3242, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC53 pattern childGuard
    simpa only [d3242, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC55 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) ≤ (0 : Int) + 3
  decide
theorem goalC56 (pattern : Twelve) (guard : d3244 pattern = 1) : d0 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC26 pattern childGuard
    simpa only [d3244, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC55 pattern childGuard
    simpa only [d3244, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC57 (pattern : Twelve) (guard : d3245 pattern = 1) : d0 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC54 pattern childGuard
    simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC56 pattern childGuard
    simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC58 (pattern : Twelve) (guard : d1867 pattern = 1) : d1 pattern ≤ (0 : Int) + d3 pattern := by
  change (1 : Int) ≤ (0 : Int) + 3
  decide
theorem goalC59 (pattern : Twelve) (guard : d3244 pattern = 1) : d26 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC26 pattern childGuard
    simpa only [d3244, d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC58 pattern childGuard
    simpa only [d3244, d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC60 (pattern : Twelve) (guard : d3247 pattern = 1) : d27 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d27, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC37 pattern childGuard
    simpa only [d3247, d27, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d27, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4591 pattern childGuard
    simpa only [d3247, d27, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC61 (pattern : Twelve) (guard : d3248 pattern = 1) : d50 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC59 pattern childGuard
    simpa only [d3248, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC60 pattern childGuard
    simpa only [d3248, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC62 (pattern : Twelve) (guard : d3249 pattern = 1) : d72 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC57 pattern childGuard
    simpa only [d3249, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC61 pattern childGuard
    simpa only [d3249, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC63 (pattern : Twelve) (guard : d3247 pattern = 1) : d0 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC42 pattern childGuard
    simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2915 pattern childGuard
    simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC64 (pattern : Twelve) (guard : d3248 pattern = 1) : d0 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC56 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC63 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC65 (pattern : Twelve) (guard : d3252 pattern = 1) : d76 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC64 pattern childGuard
    simpa only [d3252, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC49 pattern childGuard
    simpa only [d3252, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC66 (pattern : Twelve) (guard : d3253 pattern = 1) : d93 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC62 pattern childGuard
    simpa only [d3253, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC65 pattern childGuard
    simpa only [d3253, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC67 (pattern : Twelve) (guard : d3241 pattern = 1) : d0 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) ≤ (0 : Int) + 4
  decide
theorem goalC68 (pattern : Twelve) (guard : d1867 pattern = 1) : d2 pattern ≤ (0 : Int) + d5 pattern := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem goalC69 (pattern : Twelve) (guard : d3244 pattern = 1) : d30 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d30, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC67 pattern childGuard
    simpa only [d3244, d30, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d30, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC68 pattern childGuard
    simpa only [d3244, d30, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC70 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) ≤ (0 : Int) + 4
  decide
theorem goalC71 (pattern : Twelve) (guard : d3247 pattern = 1) : d35 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d35, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC70 pattern childGuard
    simpa only [d3247, d35, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d35, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d3247, d35, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC72 (pattern : Twelve) (guard : d3248 pattern = 1) : d56 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC69 pattern childGuard
    simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC71 pattern childGuard
    simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC73 (pattern : Twelve) (guard : d3247 pattern = 1) : d30 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d30, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC70 pattern childGuard
    simpa only [d3247, d30, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d30, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3355 pattern childGuard
    simpa only [d3247, d30, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC74 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC75 (pattern : Twelve) (guard : d3251 pattern = 1) : d57 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC73 pattern childGuard
    simpa only [d3251, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC74 pattern childGuard
    simpa only [d3251, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC76 (pattern : Twelve) (guard : d3252 pattern = 1) : d77 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC72 pattern childGuard
    simpa only [d3252, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC75 pattern childGuard
    simpa only [d3252, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC77 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC78 (pattern : Twelve) (guard : d3251 pattern = 1) : d56 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC73 pattern childGuard
    simpa only [d3251, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC77 pattern childGuard
    simpa only [d3251, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC79 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC80 (pattern : Twelve) (guard : d3255 pattern = 1) : d78 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC78 pattern childGuard
    simpa only [d3255, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC79 pattern childGuard
    simpa only [d3255, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC81 (pattern : Twelve) (guard : d3256 pattern = 1) : d94 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC76 pattern childGuard
    simpa only [d3256, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC80 pattern childGuard
    simpa only [d3256, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC82 (pattern : Twelve) (guard : d3257 pattern = 1) : d103 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d103, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC66 pattern childGuard
    simpa only [d3257, d103, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d103, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC81 pattern childGuard
    simpa only [d3257, d103, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC83 (pattern : Twelve) (guard : d3258 pattern = 1) : d110 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d110, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC52 pattern childGuard
    simpa only [d3258, d110, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d110, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC82 pattern childGuard
    simpa only [d3258, d110, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC84 (pattern : Twelve) (guard : d3241 pattern = 1) : d2 pattern ≤ (0 : Int) + d4 pattern := by
  change (2 : Int) ≤ (0 : Int) + 4
  decide
theorem goalC85 (pattern : Twelve) (guard : d3242 pattern = 1) : d30 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d3242, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC84 pattern childGuard
    simpa only [d3242, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC86 (pattern : Twelve) (guard : d1867 pattern = 1) : d2 pattern ≤ (0 : Int) + d4 pattern := by
  change (2 : Int) ≤ (0 : Int) + 4
  decide
theorem goalC87 (pattern : Twelve) (guard : d3244 pattern = 1) : d30 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC53 pattern childGuard
    simpa only [d3244, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC86 pattern childGuard
    simpa only [d3244, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC88 (pattern : Twelve) (guard : d3245 pattern = 1) : d30 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC85 pattern childGuard
    simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC87 pattern childGuard
    simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC89 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) ≤ (0 : Int) + 3
  decide
theorem goalC90 (pattern : Twelve) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC91 (pattern : Twelve) (guard : d1867 pattern = 1) : d17 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC89 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC90 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC92 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC93 (pattern : Twelve) (guard : d3247 pattern = 1) : d37 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d37, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC91 pattern childGuard
    simpa only [d3247, d37, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d37, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC92 pattern childGuard
    simpa only [d3247, d37, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC94 (pattern : Twelve) (guard : d3248 pattern = 1) : d58 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC87 pattern childGuard
    simpa only [d3248, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC93 pattern childGuard
    simpa only [d3248, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC95 (pattern : Twelve) (guard : d3249 pattern = 1) : d79 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC88 pattern childGuard
    simpa only [d3249, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC94 pattern childGuard
    simpa only [d3249, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC96 (pattern : Twelve) (guard : d3247 pattern = 1) : d30 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC55 pattern childGuard
    simpa only [d3247, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3340 pattern childGuard
    simpa only [d3247, d30, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC97 (pattern : Twelve) (guard : d3248 pattern = 1) : d30 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC87 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC96 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC98 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC99 (pattern : Twelve) (guard : d3247 pattern = 1) : d34 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d34, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC91 pattern childGuard
    simpa only [d3247, d34, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d34, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC98 pattern childGuard
    simpa only [d3247, d34, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC100 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC101 (pattern : Twelve) (guard : d3251 pattern = 1) : d55 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC99 pattern childGuard
    simpa only [d3251, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC100 pattern childGuard
    simpa only [d3251, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC102 (pattern : Twelve) (guard : d3252 pattern = 1) : d80 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC97 pattern childGuard
    simpa only [d3252, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC101 pattern childGuard
    simpa only [d3252, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC103 (pattern : Twelve) (guard : d3253 pattern = 1) : d95 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC95 pattern childGuard
    simpa only [d3253, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC102 pattern childGuard
    simpa only [d3253, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC104 (pattern : Twelve) (guard : d3241 pattern = 1) : d2 pattern ≤ (0 : Int) + d5 pattern := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem goalC105 (pattern : Twelve) (guard : d1867 pattern = 1) : d4 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range4 pattern).2
  change d4 pattern ≤ (0 : Int) + 6
  omega
theorem goalC106 (pattern : Twelve) (guard : d3244 pattern = 1) : d38 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d38, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC104 pattern childGuard
    simpa only [d3244, d38, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d38, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC105 pattern childGuard
    simpa only [d3244, d38, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC107 (pattern : Twelve) (guard : d3247 pattern = 1) : d39 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d39, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC68 pattern childGuard
    simpa only [d3247, d39, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d39, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3247, d39, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC108 (pattern : Twelve) (guard : d3248 pattern = 1) : d59 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC106 pattern childGuard
    simpa only [d3248, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC107 pattern childGuard
    simpa only [d3248, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC109 (pattern : Twelve) (guard : d3247 pattern = 1) : d38 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d38, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC68 pattern childGuard
    simpa only [d3247, d38, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d38, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1334 pattern childGuard
    simpa only [d3247, d38, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC110 (pattern : Twelve) (guard : d0 pattern = 1) : d40 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC111 (pattern : Twelve) (guard : d3251 pattern = 1) : d60 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC109 pattern childGuard
    simpa only [d3251, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC110 pattern childGuard
    simpa only [d3251, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC112 (pattern : Twelve) (guard : d3252 pattern = 1) : d81 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC108 pattern childGuard
    simpa only [d3252, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC111 pattern childGuard
    simpa only [d3252, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC113 (pattern : Twelve) (guard : d0 pattern = 1) : d39 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC114 (pattern : Twelve) (guard : d3251 pattern = 1) : d59 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC109 pattern childGuard
    simpa only [d3251, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC113 pattern childGuard
    simpa only [d3251, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC115 (pattern : Twelve) (guard : d0 pattern = 1) : d61 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC116 (pattern : Twelve) (guard : d3255 pattern = 1) : d82 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC114 pattern childGuard
    simpa only [d3255, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC115 pattern childGuard
    simpa only [d3255, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC117 (pattern : Twelve) (guard : d3256 pattern = 1) : d96 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC112 pattern childGuard
    simpa only [d3256, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC116 pattern childGuard
    simpa only [d3256, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC118 (pattern : Twelve) (guard : d3257 pattern = 1) : d104 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d104, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC103 pattern childGuard
    simpa only [d3257, d104, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d104, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC117 pattern childGuard
    simpa only [d3257, d104, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC119 (pattern : Twelve) (guard : d3241 pattern = 1) : d0 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem goalC120 (pattern : Twelve) (guard : d1867 pattern = 1) : d2 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range2 pattern).2
  change d2 pattern ≤ (0 : Int) + 6
  omega
theorem goalC121 (pattern : Twelve) (guard : d3244 pattern = 1) : d30 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d30, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC119 pattern childGuard
    simpa only [d3244, d30, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d30, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC120 pattern childGuard
    simpa only [d3244, d30, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC122 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem goalC123 (pattern : Twelve) (guard : d3247 pattern = 1) : d35 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d35, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC122 pattern childGuard
    simpa only [d3247, d35, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d35, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3247, d35, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC124 (pattern : Twelve) (guard : d3248 pattern = 1) : d56 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC121 pattern childGuard
    simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC123 pattern childGuard
    simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC125 (pattern : Twelve) (guard : d3247 pattern = 1) : d30 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d30, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC122 pattern childGuard
    simpa only [d3247, d30, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d30, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1311 pattern childGuard
    simpa only [d3247, d30, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC126 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC127 (pattern : Twelve) (guard : d3251 pattern = 1) : d57 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC125 pattern childGuard
    simpa only [d3251, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC126 pattern childGuard
    simpa only [d3251, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC128 (pattern : Twelve) (guard : d3252 pattern = 1) : d77 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC124 pattern childGuard
    simpa only [d3252, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC127 pattern childGuard
    simpa only [d3252, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC129 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
