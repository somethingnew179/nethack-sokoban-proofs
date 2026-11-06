/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons03
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC520 (pattern : Twelve) (guard : d3247 pattern = 1) : d515 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d515, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC519 pattern childGuard
    simpa only [d3247, d515, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d515, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d3247, d515, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC521 (pattern : Twelve) (guard : d3248 pattern = 1) : d543 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC517 pattern childGuard
    simpa only [d3248, d543, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC520 pattern childGuard
    simpa only [d3248, d543, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC522 (pattern : Twelve) (guard : d0 pattern = 1) : d487 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC523 (pattern : Twelve) (guard : d3247 pattern = 1) : d509 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d509, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC519 pattern childGuard
    simpa only [d3247, d509, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d509, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC522 pattern childGuard
    simpa only [d3247, d509, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC524 (pattern : Twelve) (guard : d0 pattern = 1) : d515 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC525 (pattern : Twelve) (guard : d3251 pattern = 1) : d544 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC523 pattern childGuard
    simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC524 pattern childGuard
    simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC526 (pattern : Twelve) (guard : d3252 pattern = 1) : d567 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC521 pattern childGuard
    simpa only [d3252, d567, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC525 pattern childGuard
    simpa only [d3252, d567, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC527 (pattern : Twelve) (guard : d0 pattern = 1) : d539 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC528 (pattern : Twelve) (guard : d3255 pattern = 1) : d568 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC525 pattern childGuard
    simpa only [d3255, d568, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC527 pattern childGuard
    simpa only [d3255, d568, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC529 (pattern : Twelve) (guard : d3256 pattern = 1) : d591 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC526 pattern childGuard
    simpa only [d3256, d591, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC528 pattern childGuard
    simpa only [d3256, d591, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC530 (pattern : Twelve) (guard : d3257 pattern = 1) : d607 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d607, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC513 pattern childGuard
    simpa only [d3257, d607, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d607, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC529 pattern childGuard
    simpa only [d3257, d607, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC531 (pattern : Twelve) (guard : d3258 pattern = 1) : d618 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d618, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC496 pattern childGuard
    simpa only [d3258, d618, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d618, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC530 pattern childGuard
    simpa only [d3258, d618, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC532 (pattern : Twelve) (guard : d1 pattern = 1) : d490 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC533 (pattern : Twelve) (guard : d3241 pattern = 1) : d491 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d3241, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d3241, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC534 (pattern : Twelve) (guard : d3242 pattern = 1) : d516 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d516, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC532 pattern childGuard
    simpa only [d3242, d516, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d516, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC533 pattern childGuard
    simpa only [d3242, d516, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC535 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d4 pattern := by
  change (2 : Int) ≤ (0 : Int) + 4
  decide
theorem goalC536 (pattern : Twelve) (guard : d1867 pattern = 1) : d487 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC535 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC537 (pattern : Twelve) (guard : d3244 pattern = 1) : d517 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d517, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC497 pattern childGuard
    simpa only [d3244, d517, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d517, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC536 pattern childGuard
    simpa only [d3244, d517, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC538 (pattern : Twelve) (guard : d3245 pattern = 1) : d545 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC534 pattern childGuard
    simpa only [d3245, d545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC537 pattern childGuard
    simpa only [d3245, d545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC539 (pattern : Twelve) (guard : d0 pattern = 1) : d492 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC540 (pattern : Twelve) (guard : d3247 pattern = 1) : d518 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d518, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC499 pattern childGuard
    simpa only [d3247, d518, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d518, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC539 pattern childGuard
    simpa only [d3247, d518, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC541 (pattern : Twelve) (guard : d3248 pattern = 1) : d546 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC537 pattern childGuard
    simpa only [d3248, d546, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC540 pattern childGuard
    simpa only [d3248, d546, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC542 (pattern : Twelve) (guard : d3249 pattern = 1) : d569 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC538 pattern childGuard
    simpa only [d3249, d569, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC541 pattern childGuard
    simpa only [d3249, d569, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC543 (pattern : Twelve) (guard : d0 pattern = 1) : d487 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC544 (pattern : Twelve) (guard : d3247 pattern = 1) : d509 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d509, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC499 pattern childGuard
    simpa only [d3247, d509, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d509, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC543 pattern childGuard
    simpa only [d3247, d509, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC545 (pattern : Twelve) (guard : d3248 pattern = 1) : d547 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC537 pattern childGuard
    simpa only [d3248, d547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC544 pattern childGuard
    simpa only [d3248, d547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC546 (pattern : Twelve) (guard : d0 pattern = 1) : d503 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC547 (pattern : Twelve) (guard : d3251 pattern = 1) : d539 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC544 pattern childGuard
    simpa only [d3251, d539, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC546 pattern childGuard
    simpa only [d3251, d539, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC548 (pattern : Twelve) (guard : d3252 pattern = 1) : d570 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC545 pattern childGuard
    simpa only [d3252, d570, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC547 pattern childGuard
    simpa only [d3252, d570, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC549 (pattern : Twelve) (guard : d3253 pattern = 1) : d592 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC542 pattern childGuard
    simpa only [d3253, d592, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC548 pattern childGuard
    simpa only [d3253, d592, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC550 (pattern : Twelve) (guard : d3241 pattern = 1) : d493 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d3241, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d3241, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC551 (pattern : Twelve) (guard : d1867 pattern = 1) : d494 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range494 pattern).2
  change d494 pattern ≤ (0 : Int) + 6
  omega
theorem goalC552 (pattern : Twelve) (guard : d3244 pattern = 1) : d519 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d519, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC550 pattern childGuard
    simpa only [d3244, d519, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d519, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC551 pattern childGuard
    simpa only [d3244, d519, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC553 (pattern : Twelve) (guard : d3247 pattern = 1) : d520 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d520, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC516 pattern childGuard
    simpa only [d3247, d520, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d520, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3247, d520, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC554 (pattern : Twelve) (guard : d3248 pattern = 1) : d548 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC552 pattern childGuard
    simpa only [d3248, d548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC553 pattern childGuard
    simpa only [d3248, d548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC555 (pattern : Twelve) (guard : d0 pattern = 1) : d494 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC556 (pattern : Twelve) (guard : d3247 pattern = 1) : d521 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d521, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC516 pattern childGuard
    simpa only [d3247, d521, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d521, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC555 pattern childGuard
    simpa only [d3247, d521, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC557 (pattern : Twelve) (guard : d0 pattern = 1) : d520 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC558 (pattern : Twelve) (guard : d3251 pattern = 1) : d549 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC556 pattern childGuard
    simpa only [d3251, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC557 pattern childGuard
    simpa only [d3251, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC559 (pattern : Twelve) (guard : d3252 pattern = 1) : d571 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC554 pattern childGuard
    simpa only [d3252, d571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC558 pattern childGuard
    simpa only [d3252, d571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC560 (pattern : Twelve) (guard : d0 pattern = 1) : d550 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC561 (pattern : Twelve) (guard : d3255 pattern = 1) : d572 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC558 pattern childGuard
    simpa only [d3255, d572, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC560 pattern childGuard
    simpa only [d3255, d572, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC562 (pattern : Twelve) (guard : d3256 pattern = 1) : d593 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC559 pattern childGuard
    simpa only [d3256, d593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC561 pattern childGuard
    simpa only [d3256, d593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC563 (pattern : Twelve) (guard : d3257 pattern = 1) : d608 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d608, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC549 pattern childGuard
    simpa only [d3257, d608, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d608, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC562 pattern childGuard
    simpa only [d3257, d608, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC564 (pattern : Twelve) (guard : d3241 pattern = 1) : d496 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16662 pattern childGuard
    simpa only [d3241, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d3241, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC565 (pattern : Twelve) (guard : d1867 pattern = 1) : d487 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range487 pattern).2
  change d487 pattern ≤ (0 : Int) + 6
  omega
theorem goalC566 (pattern : Twelve) (guard : d3244 pattern = 1) : d523 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d523, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC564 pattern childGuard
    simpa only [d3244, d523, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d523, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC565 pattern childGuard
    simpa only [d3244, d523, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC567 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem goalC568 (pattern : Twelve) (guard : d1867 pattern = 1) : d480 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC567 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC569 (pattern : Twelve) (guard : d3247 pattern = 1) : d515 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d515, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC568 pattern childGuard
    simpa only [d3247, d515, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d515, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3247, d515, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC570 (pattern : Twelve) (guard : d3248 pattern = 1) : d551 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC566 pattern childGuard
    simpa only [d3248, d551, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC569 pattern childGuard
    simpa only [d3248, d551, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC571 (pattern : Twelve) (guard : d0 pattern = 1) : d487 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC572 (pattern : Twelve) (guard : d3247 pattern = 1) : d509 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d509, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC568 pattern childGuard
    simpa only [d3247, d509, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d509, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC571 pattern childGuard
    simpa only [d3247, d509, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC573 (pattern : Twelve) (guard : d0 pattern = 1) : d515 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC574 (pattern : Twelve) (guard : d3251 pattern = 1) : d544 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC572 pattern childGuard
    simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC573 pattern childGuard
    simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC575 (pattern : Twelve) (guard : d3252 pattern = 1) : d573 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC570 pattern childGuard
    simpa only [d3252, d573, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC574 pattern childGuard
    simpa only [d3252, d573, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC576 (pattern : Twelve) (guard : d0 pattern = 1) : d539 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC577 (pattern : Twelve) (guard : d3255 pattern = 1) : d568 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC574 pattern childGuard
    simpa only [d3255, d568, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC576 pattern childGuard
    simpa only [d3255, d568, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC578 (pattern : Twelve) (guard : d3256 pattern = 1) : d594 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC575 pattern childGuard
    simpa only [d3256, d594, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC577 pattern childGuard
    simpa only [d3256, d594, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC579 (pattern : Twelve) (guard : d3260 pattern = 1) : d609 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d609, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC578 pattern childGuard
    simpa only [d3260, d609, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d609, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d609, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC580 (pattern : Twelve) (guard : d3261 pattern = 1) : d619 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d619, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC563 pattern childGuard
    simpa only [d3261, d619, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d619, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC579 pattern childGuard
    simpa only [d3261, d619, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC581 (pattern : Twelve) (guard : d3262 pattern = 1) : d624 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d624, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC531 pattern childGuard
    simpa only [d3262, d624, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d624, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC580 pattern childGuard
    simpa only [d3262, d624, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC582 (pattern : Twelve) (guard : d3265 pattern = 1) : d625 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range625 pattern).2
  change d625 pattern ≤ (0 : Int) + 6
  omega
theorem goalC583 (pattern : Twelve) (guard : d3266 pattern = 1) : d627 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d627, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC581 pattern childGuard
    simpa only [d3266, d627, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d627, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC582 pattern childGuard
    simpa only [d3266, d627, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC584 (pattern : Twelve) (guard : d3269 pattern = 1) : d625 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range625 pattern).2
  change d625 pattern ≤ (0 : Int) + 6
  omega
theorem goalC585 (pattern : Twelve) (guard : d3270 pattern = 1) : d628 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d628, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC583 pattern childGuard
    simpa only [d3270, d628, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d628, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC584 pattern childGuard
    simpa only [d3270, d628, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC586 (pattern : Twelve) (guard : d3273 pattern = 1) : d626 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range626 pattern).2
  change d626 pattern ≤ (0 : Int) + 6
  omega
theorem goalC587 (pattern : Twelve) (guard : d3274 pattern = 1) : d629 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d629, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC585 pattern childGuard
    simpa only [d3274, d629, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d629, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC586 pattern childGuard
    simpa only [d3274, d629, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC588 (pattern : Twelve) (guard : d1 pattern = 1) : d646 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d646, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d646, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d646, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10901 pattern childGuard
    simpa only [d646, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC589 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC590 (pattern : Twelve) (guard : d3241 pattern = 1) : d634 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10901 pattern childGuard
    simpa only [d3241, d634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC589 pattern childGuard
    simpa only [d3241, d634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC591 (pattern : Twelve) (guard : d3242 pattern = 1) : d647 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d647, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d3242, d647, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d647, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC590 pattern childGuard
    simpa only [d3242, d647, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC592 (pattern : Twelve) (guard : d3243 pattern = 1) : d680 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3243, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC588 pattern childGuard
    simpa only [d3243, d680, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3243, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC591 pattern childGuard
    simpa only [d3243, d680, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC593 (pattern : Twelve) (guard : d3244 pattern = 1) : d648 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d648, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC153 pattern childGuard
    simpa only [d3244, d648, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d648, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8480 pattern childGuard
    simpa only [d3244, d648, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC594 (pattern : Twelve) (guard : d3245 pattern = 1) : d681 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC151 pattern childGuard
    simpa only [d3245, d681, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC593 pattern childGuard
    simpa only [d3245, d681, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC595 (pattern : Twelve) (guard : d3246 pattern = 1) : d709 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3243 pattern = 1 := by simpa only [d3246, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC592 pattern childGuard
    simpa only [d3246, d709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3246, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC594 pattern childGuard
    simpa only [d3246, d709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC596 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC597 (pattern : Twelve) (guard : d1867 pattern = 1) : d158 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC589 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC596 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC598 (pattern : Twelve) (guard : d3244 pattern = 1) : d649 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d649, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC153 pattern childGuard
    simpa only [d3244, d649, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d649, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC597 pattern childGuard
    simpa only [d3244, d649, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC599 (pattern : Twelve) (guard : d3245 pattern = 1) : d682 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC591 pattern childGuard
    simpa only [d3245, d682, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC598 pattern childGuard
    simpa only [d3245, d682, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC600 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC601 (pattern : Twelve) (guard : d1867 pattern = 1) : d635 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d1867, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC600 pattern childGuard
    simpa only [d1867, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC602 (pattern : Twelve) (guard : d3244 pattern = 1) : d650 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d650, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC153 pattern childGuard
    simpa only [d3244, d650, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d650, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC601 pattern childGuard
    simpa only [d3244, d650, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC603 (pattern : Twelve) (guard : d1867 pattern = 1) : d636 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d1867, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6981 pattern childGuard
    simpa only [d1867, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC604 (pattern : Twelve) (guard : d3247 pattern = 1) : d651 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d651, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC603 pattern childGuard
    simpa only [d3247, d651, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d651, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d3247, d651, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC605 (pattern : Twelve) (guard : d3248 pattern = 1) : d683 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC602 pattern childGuard
    simpa only [d3248, d683, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC604 pattern childGuard
    simpa only [d3248, d683, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC606 (pattern : Twelve) (guard : d3249 pattern = 1) : d710 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC599 pattern childGuard
    simpa only [d3249, d710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC605 pattern childGuard
    simpa only [d3249, d710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC607 (pattern : Twelve) (guard : d3250 pattern = 1) : d736 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3246 pattern = 1 := by simpa only [d3250, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC595 pattern childGuard
    simpa only [d3250, d736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3250, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC606 pattern childGuard
    simpa only [d3250, d736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC608 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10963 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC609 (pattern : Twelve) (guard : d1866 pattern = 1) : d160 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10963 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC610 (pattern : Twelve) (guard : d3241 pattern = 1) : d637 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC608 pattern childGuard
    simpa only [d3241, d637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC609 pattern childGuard
    simpa only [d3241, d637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC611 (pattern : Twelve) (guard : d3242 pattern = 1) : d652 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d652, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10907 pattern childGuard
    simpa only [d3242, d652, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d652, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC610 pattern childGuard
    simpa only [d3242, d652, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC612 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC613 (pattern : Twelve) (guard : d3241 pattern = 1) : d638 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10907 pattern childGuard
    simpa only [d3241, d638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC612 pattern childGuard
    simpa only [d3241, d638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC614 (pattern : Twelve) (guard : d1867 pattern = 1) : d639 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d1867, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC29 pattern childGuard
    simpa only [d1867, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC615 (pattern : Twelve) (guard : d3244 pattern = 1) : d653 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d653, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC613 pattern childGuard
    simpa only [d3244, d653, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d653, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC614 pattern childGuard
    simpa only [d3244, d653, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC616 (pattern : Twelve) (guard : d3245 pattern = 1) : d684 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC611 pattern childGuard
    simpa only [d3245, d684, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC615 pattern childGuard
    simpa only [d3245, d684, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC617 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC618 (pattern : Twelve) (guard : d1867 pattern = 1) : d160 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC609 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC617 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC619 (pattern : Twelve) (guard : d3244 pattern = 1) : d654 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d654, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC613 pattern childGuard
    simpa only [d3244, d654, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d654, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC618 pattern childGuard
    simpa only [d3244, d654, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC620 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC621 (pattern : Twelve) (guard : d1867 pattern = 1) : d158 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC612 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC620 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC622 (pattern : Twelve) (guard : d3247 pattern = 1) : d655 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d655, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC621 pattern childGuard
    simpa only [d3247, d655, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d655, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC38 pattern childGuard
    simpa only [d3247, d655, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC623 (pattern : Twelve) (guard : d3248 pattern = 1) : d685 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC619 pattern childGuard
    simpa only [d3248, d685, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC622 pattern childGuard
    simpa only [d3248, d685, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC624 (pattern : Twelve) (guard : d3249 pattern = 1) : d711 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC616 pattern childGuard
    simpa only [d3249, d711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC623 pattern childGuard
    simpa only [d3249, d711, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC625 (pattern : Twelve) (guard : d3247 pattern = 1) : d656 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d656, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC621 pattern childGuard
    simpa only [d3247, d656, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d656, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC43 pattern childGuard
    simpa only [d3247, d656, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC626 (pattern : Twelve) (guard : d3248 pattern = 1) : d686 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC619 pattern childGuard
    simpa only [d3248, d686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC625 pattern childGuard
    simpa only [d3248, d686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC627 (pattern : Twelve) (guard : d3247 pattern = 1) : d657 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d657, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC621 pattern childGuard
    simpa only [d3247, d657, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d657, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC617 pattern childGuard
    simpa only [d3247, d657, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC628 (pattern : Twelve) (guard : d0 pattern = 1) : d651 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC629 (pattern : Twelve) (guard : d3251 pattern = 1) : d687 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC627 pattern childGuard
    simpa only [d3251, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC628 pattern childGuard
    simpa only [d3251, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC630 (pattern : Twelve) (guard : d3252 pattern = 1) : d712 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC626 pattern childGuard
    simpa only [d3252, d712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC629 pattern childGuard
    simpa only [d3252, d712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC631 (pattern : Twelve) (guard : d3253 pattern = 1) : d737 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC624 pattern childGuard
    simpa only [d3253, d737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC630 pattern childGuard
    simpa only [d3253, d737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC632 (pattern : Twelve) (guard : d3254 pattern = 1) : d754 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d754, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC607 pattern childGuard
    simpa only [d3254, d754, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d754, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC631 pattern childGuard
    simpa only [d3254, d754, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC633 (pattern : Twelve) (guard : d1 pattern = 1) : d630 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC634 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC635 (pattern : Twelve) (guard : d3241 pattern = 1) : d640 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC633 pattern childGuard
    simpa only [d3241, d640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC634 pattern childGuard
    simpa only [d3241, d640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC636 (pattern : Twelve) (guard : d3242 pattern = 1) : d658 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d658, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10907 pattern childGuard
    simpa only [d3242, d658, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d658, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC635 pattern childGuard
    simpa only [d3242, d658, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC637 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC638 (pattern : Twelve) (guard : d1867 pattern = 1) : d158 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC634 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC637 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC639 (pattern : Twelve) (guard : d3244 pattern = 1) : d659 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d659, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC613 pattern childGuard
    simpa only [d3244, d659, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d659, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC638 pattern childGuard
    simpa only [d3244, d659, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC640 (pattern : Twelve) (guard : d3245 pattern = 1) : d688 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC636 pattern childGuard
    simpa only [d3245, d688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC639 pattern childGuard
    simpa only [d3245, d688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC641 (pattern : Twelve) (guard : d1866 pattern = 1) : d157 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC642 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC643 (pattern : Twelve) (guard : d1867 pattern = 1) : d157 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC641 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC642 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC644 (pattern : Twelve) (guard : d3244 pattern = 1) : d660 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d660, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC613 pattern childGuard
    simpa only [d3244, d660, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d660, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC643 pattern childGuard
    simpa only [d3244, d660, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC645 (pattern : Twelve) (guard : d3247 pattern = 1) : d661 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d661, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC621 pattern childGuard
    simpa only [d3247, d661, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d661, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC642 pattern childGuard
    simpa only [d3247, d661, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC646 (pattern : Twelve) (guard : d3248 pattern = 1) : d689 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC644 pattern childGuard
    simpa only [d3248, d689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC645 pattern childGuard
    simpa only [d3248, d689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC647 (pattern : Twelve) (guard : d3249 pattern = 1) : d713 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC640 pattern childGuard
    simpa only [d3249, d713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC646 pattern childGuard
    simpa only [d3249, d713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC648 (pattern : Twelve) (guard : d3247 pattern = 1) : d158 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC621 pattern childGuard
    simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC637 pattern childGuard
    simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC649 (pattern : Twelve) (guard : d3248 pattern = 1) : d690 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC639 pattern childGuard
    simpa only [d3248, d690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC648 pattern childGuard
    simpa only [d3248, d690, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
