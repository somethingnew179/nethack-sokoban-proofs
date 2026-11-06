/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons10
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC1430 (pattern : Twelve) (guard : d3259 pattern = 1) : d1679 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1182 pattern childGuard
    simpa only [d3259, d1679, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3259, d1679, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1431 (pattern : Twelve) (guard : d3263 pattern = 1) : d1680 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1680, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1430 pattern childGuard
    simpa only [d3263, d1680, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1680, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3263, d1680, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1432 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1433 (pattern : Twelve) (guard : d3267 pattern = 1) : d1681 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1681, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1431 pattern childGuard
    simpa only [d3267, d1681, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1681, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1432 pattern childGuard
    simpa only [d3267, d1681, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1434 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1435 (pattern : Twelve) (guard : d3271 pattern = 1) : d1682 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1682, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1433 pattern childGuard
    simpa only [d3271, d1682, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1682, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1434 pattern childGuard
    simpa only [d3271, d1682, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1436 (pattern : Twelve) (guard : d3275 pattern = 1) : d1683 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d1683, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1435 pattern childGuard
    simpa only [d3275, d1683, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d1683, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3275, d1683, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1437 (pattern : Twelve) (guard : d3278 pattern = 1) : d1684 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d1684, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1436 pattern childGuard
    simpa only [d3278, d1684, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d1684, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3278, d1684, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1438 (pattern : Twelve) (guard : d3280 pattern = 1) : d1685 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1685, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1437 pattern childGuard
    simpa only [d3280, d1685, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1685, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3280, d1685, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1439 (pattern : Twelve) (guard : d3267 pattern = 1) : d1686 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1686, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1421 pattern childGuard
    simpa only [d3267, d1686, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1686, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1432 pattern childGuard
    simpa only [d3267, d1686, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1440 (pattern : Twelve) (guard : d0 pattern = 1) : d1687 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1441 (pattern : Twelve) (guard : d3271 pattern = 1) : d1688 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1688, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1439 pattern childGuard
    simpa only [d3271, d1688, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1688, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1440 pattern childGuard
    simpa only [d3271, d1688, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1442 (pattern : Twelve) (guard : d0 pattern = 1) : d1688 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1443 (pattern : Twelve) (guard : d3275 pattern = 1) : d1688 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1441 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1442 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1444 (pattern : Twelve) (guard : d3278 pattern = 1) : d1688 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1443 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1442 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1445 (pattern : Twelve) (guard : d3280 pattern = 1) : d1688 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1444 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1442 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1446 (pattern : Twelve) (guard : d0 pattern = 1) : d1689 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1447 (pattern : Twelve) (guard : d3255 pattern = 1) : d1693 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1210 pattern childGuard
    simpa only [d3255, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1446 pattern childGuard
    simpa only [d3255, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1448 (pattern : Twelve) (guard : d0 pattern = 1) : d1694 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1449 (pattern : Twelve) (guard : d3259 pattern = 1) : d1697 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1447 pattern childGuard
    simpa only [d3259, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1448 pattern childGuard
    simpa only [d3259, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1450 (pattern : Twelve) (guard : d0 pattern = 1) : d1698 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1451 (pattern : Twelve) (guard : d3263 pattern = 1) : d1700 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1700, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1449 pattern childGuard
    simpa only [d3263, d1700, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1700, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1450 pattern childGuard
    simpa only [d3263, d1700, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1452 (pattern : Twelve) (guard : d0 pattern = 1) : d1700 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1453 (pattern : Twelve) (guard : d3267 pattern = 1) : d1700 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1451 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1452 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1454 (pattern : Twelve) (guard : d0 pattern = 1) : d1703 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1455 (pattern : Twelve) (guard : d3271 pattern = 1) : d1704 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1704, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1453 pattern childGuard
    simpa only [d3271, d1704, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1704, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1454 pattern childGuard
    simpa only [d3271, d1704, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1456 (pattern : Twelve) (guard : d0 pattern = 1) : d1704 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1457 (pattern : Twelve) (guard : d3275 pattern = 1) : d1704 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1455 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1456 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1458 (pattern : Twelve) (guard : d3278 pattern = 1) : d1704 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1457 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1456 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1459 (pattern : Twelve) (guard : d3280 pattern = 1) : d1704 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1458 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1456 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1460 (pattern : Twelve) (guard : d3259 pattern = 1) : d1705 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1417 pattern childGuard
    simpa only [d3259, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3259, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1461 (pattern : Twelve) (guard : d0 pattern = 1) : d1706 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1462 (pattern : Twelve) (guard : d3263 pattern = 1) : d1709 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1709, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1460 pattern childGuard
    simpa only [d3263, d1709, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1709, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1461 pattern childGuard
    simpa only [d3263, d1709, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1463 (pattern : Twelve) (guard : d0 pattern = 1) : d1709 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1464 (pattern : Twelve) (guard : d3267 pattern = 1) : d1709 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1462 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1463 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1465 (pattern : Twelve) (guard : d0 pattern = 1) : d1712 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1466 (pattern : Twelve) (guard : d3271 pattern = 1) : d1713 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1713, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1464 pattern childGuard
    simpa only [d3271, d1713, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1713, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1465 pattern childGuard
    simpa only [d3271, d1713, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1467 (pattern : Twelve) (guard : d0 pattern = 1) : d1713 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1468 (pattern : Twelve) (guard : d3275 pattern = 1) : d1713 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1466 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1467 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1469 (pattern : Twelve) (guard : d3278 pattern = 1) : d1713 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1468 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1467 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1470 (pattern : Twelve) (guard : d3280 pattern = 1) : d1713 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1469 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1467 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1471 (pattern : Twelve) (guard : d3271 pattern = 1) : d1714 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1714, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1423 pattern childGuard
    simpa only [d3271, d1714, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1714, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1434 pattern childGuard
    simpa only [d3271, d1714, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1472 (pattern : Twelve) (guard : d0 pattern = 1) : d1714 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1473 (pattern : Twelve) (guard : d3275 pattern = 1) : d1714 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1471 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1472 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1474 (pattern : Twelve) (guard : d3278 pattern = 1) : d1714 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1473 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1472 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1475 (pattern : Twelve) (guard : d3280 pattern = 1) : d1714 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1474 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1472 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1476 (pattern : Twelve) (guard : d3263 pattern = 1) : d1715 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1715, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1419 pattern childGuard
    simpa only [d3263, d1715, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1715, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3263, d1715, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1477 (pattern : Twelve) (guard : d0 pattern = 1) : d1715 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1478 (pattern : Twelve) (guard : d3267 pattern = 1) : d1715 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1476 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1477 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1479 (pattern : Twelve) (guard : d0 pattern = 1) : d1715 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1480 (pattern : Twelve) (guard : d3271 pattern = 1) : d1715 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1478 pattern childGuard
    simpa only [d3271, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1479 pattern childGuard
    simpa only [d3271, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1481 (pattern : Twelve) (guard : d3275 pattern = 1) : d1715 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1480 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4382 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1482 (pattern : Twelve) (guard : d3278 pattern = 1) : d1715 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1481 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4382 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1483 (pattern : Twelve) (guard : d3280 pattern = 1) : d1715 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1482 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4382 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1484 (pattern : Twelve) (guard : d0 pattern = 1) : d1645 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1485 (pattern : Twelve) (guard : d3255 pattern = 1) : d1716 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1288 pattern childGuard
    simpa only [d3255, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1484 pattern childGuard
    simpa only [d3255, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1486 (pattern : Twelve) (guard : d0 pattern = 1) : d1452 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1487 (pattern : Twelve) (guard : d3259 pattern = 1) : d1719 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1485 pattern childGuard
    simpa only [d3259, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1486 pattern childGuard
    simpa only [d3259, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1488 (pattern : Twelve) (guard : d0 pattern = 1) : d1719 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1489 (pattern : Twelve) (guard : d3263 pattern = 1) : d1719 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1487 pattern childGuard
    simpa only [d3263, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1488 pattern childGuard
    simpa only [d3263, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1490 (pattern : Twelve) (guard : d0 pattern = 1) : d1719 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1491 (pattern : Twelve) (guard : d3267 pattern = 1) : d1719 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1489 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1490 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1492 (pattern : Twelve) (guard : d0 pattern = 1) : d1725 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1493 (pattern : Twelve) (guard : d3271 pattern = 1) : d1727 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1727, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1491 pattern childGuard
    simpa only [d3271, d1727, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1727, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1492 pattern childGuard
    simpa only [d3271, d1727, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1494 (pattern : Twelve) (guard : d0 pattern = 1) : d1727 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1495 (pattern : Twelve) (guard : d3275 pattern = 1) : d1727 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1493 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1494 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1496 (pattern : Twelve) (guard : d3278 pattern = 1) : d1727 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1495 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1494 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1497 (pattern : Twelve) (guard : d0 pattern = 1) : d1728 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1498 (pattern : Twelve) (guard : d3280 pattern = 1) : d1729 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1729, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1496 pattern childGuard
    simpa only [d3280, d1729, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1729, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1497 pattern childGuard
    simpa only [d3280, d1729, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1499 (pattern : Twelve) (guard : d3259 pattern = 1) : d1730 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1147 pattern childGuard
    simpa only [d3259, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1418 pattern childGuard
    simpa only [d3259, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1500 (pattern : Twelve) (guard : d0 pattern = 1) : d1731 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1501 (pattern : Twelve) (guard : d3263 pattern = 1) : d1736 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1736, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1499 pattern childGuard
    simpa only [d3263, d1736, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1736, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1500 pattern childGuard
    simpa only [d3263, d1736, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1502 (pattern : Twelve) (guard : d0 pattern = 1) : d1736 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1503 (pattern : Twelve) (guard : d3267 pattern = 1) : d1736 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1501 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1502 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1504 (pattern : Twelve) (guard : d0 pattern = 1) : d1740 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1505 (pattern : Twelve) (guard : d3271 pattern = 1) : d1742 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1742, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1503 pattern childGuard
    simpa only [d3271, d1742, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1742, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1504 pattern childGuard
    simpa only [d3271, d1742, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1506 (pattern : Twelve) (guard : d0 pattern = 1) : d1742 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1507 (pattern : Twelve) (guard : d3275 pattern = 1) : d1742 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1505 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1506 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1508 (pattern : Twelve) (guard : d3278 pattern = 1) : d1742 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1507 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1506 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1509 (pattern : Twelve) (guard : d0 pattern = 1) : d1743 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1510 (pattern : Twelve) (guard : d3280 pattern = 1) : d1744 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1744, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1508 pattern childGuard
    simpa only [d3280, d1744, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1744, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1509 pattern childGuard
    simpa only [d3280, d1744, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1511 (pattern : Twelve) (guard : d0 pattern = 1) : d1494 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1512 (pattern : Twelve) (guard : d3255 pattern = 1) : d1753 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1339 pattern childGuard
    simpa only [d3255, d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1511 pattern childGuard
    simpa only [d3255, d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1513 (pattern : Twelve) (guard : d0 pattern = 1) : d1754 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1514 (pattern : Twelve) (guard : d3259 pattern = 1) : d1763 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1512 pattern childGuard
    simpa only [d3259, d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1513 pattern childGuard
    simpa only [d3259, d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1515 (pattern : Twelve) (guard : d0 pattern = 1) : d1764 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1516 (pattern : Twelve) (guard : d3263 pattern = 1) : d1770 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1770, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1514 pattern childGuard
    simpa only [d3263, d1770, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1770, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1515 pattern childGuard
    simpa only [d3263, d1770, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1517 (pattern : Twelve) (guard : d0 pattern = 1) : d1770 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1518 (pattern : Twelve) (guard : d3267 pattern = 1) : d1770 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1516 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1517 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1519 (pattern : Twelve) (guard : d0 pattern = 1) : d1775 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1520 (pattern : Twelve) (guard : d3271 pattern = 1) : d1777 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1777, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1518 pattern childGuard
    simpa only [d3271, d1777, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1777, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1519 pattern childGuard
    simpa only [d3271, d1777, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1521 (pattern : Twelve) (guard : d0 pattern = 1) : d1777 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1522 (pattern : Twelve) (guard : d3275 pattern = 1) : d1777 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1520 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1521 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1523 (pattern : Twelve) (guard : d3278 pattern = 1) : d1777 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1522 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1521 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1524 (pattern : Twelve) (guard : d0 pattern = 1) : d1778 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1525 (pattern : Twelve) (guard : d3280 pattern = 1) : d1779 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1779, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1523 pattern childGuard
    simpa only [d3280, d1779, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1779, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1524 pattern childGuard
    simpa only [d3280, d1779, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1526 (pattern : Twelve) (guard : d0 pattern = 1) : d635 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1527 (pattern : Twelve) (guard : d3255 pattern = 1) : d1788 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1375 pattern childGuard
    simpa only [d3255, d1788, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1526 pattern childGuard
    simpa only [d3255, d1788, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1528 (pattern : Twelve) (guard : d0 pattern = 1) : d1789 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1529 (pattern : Twelve) (guard : d3259 pattern = 1) : d1797 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1527 pattern childGuard
    simpa only [d3259, d1797, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1528 pattern childGuard
    simpa only [d3259, d1797, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1530 (pattern : Twelve) (guard : d0 pattern = 1) : d1798 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1531 (pattern : Twelve) (guard : d3263 pattern = 1) : d1804 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1804, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1529 pattern childGuard
    simpa only [d3263, d1804, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1804, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1530 pattern childGuard
    simpa only [d3263, d1804, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1532 (pattern : Twelve) (guard : d0 pattern = 1) : d1804 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1533 (pattern : Twelve) (guard : d3267 pattern = 1) : d1804 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1531 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1532 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1534 (pattern : Twelve) (guard : d0 pattern = 1) : d1809 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1535 (pattern : Twelve) (guard : d3271 pattern = 1) : d1811 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1811, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1533 pattern childGuard
    simpa only [d3271, d1811, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1811, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1534 pattern childGuard
    simpa only [d3271, d1811, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1536 (pattern : Twelve) (guard : d0 pattern = 1) : d1811 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1537 (pattern : Twelve) (guard : d3275 pattern = 1) : d1811 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1535 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1536 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1538 (pattern : Twelve) (guard : d3278 pattern = 1) : d1811 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1537 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1536 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1539 (pattern : Twelve) (guard : d0 pattern = 1) : d1812 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1540 (pattern : Twelve) (guard : d3280 pattern = 1) : d1813 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1813, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1538 pattern childGuard
    simpa only [d3280, d1813, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1813, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1539 pattern childGuard
    simpa only [d3280, d1813, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1541 (pattern : Twelve) (guard : d3280 pattern = 1) : d1827 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1827, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1427 pattern childGuard
    simpa only [d3280, d1827, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1827, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9646 pattern childGuard
    simpa only [d3280, d1827, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1542 (pattern : Twelve) (guard : d3275 pattern = 1) : d1828 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d1828, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1425 pattern childGuard
    simpa only [d3275, d1828, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d1828, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3275, d1828, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1543 (pattern : Twelve) (guard : d3278 pattern = 1) : d1828 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1542 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9724 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1544 (pattern : Twelve) (guard : d3280 pattern = 1) : d1830 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1830, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1543 pattern childGuard
    simpa only [d3280, d1830, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1830, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9726 pattern childGuard
    simpa only [d3280, d1830, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1545 (pattern : Twelve) (guard : d3278 pattern = 1) : d1831 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d1831, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1426 pattern childGuard
    simpa only [d3278, d1831, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d1831, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3278, d1831, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1546 (pattern : Twelve) (guard : d0 pattern = 1) : d1832 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1547 (pattern : Twelve) (guard : d3280 pattern = 1) : d1833 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1833, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1545 pattern childGuard
    simpa only [d3280, d1833, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1833, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1546 pattern childGuard
    simpa only [d3280, d1833, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1548 (pattern : Twelve) (guard : d3280 pattern = 1) : d1834 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1834, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1427 pattern childGuard
    simpa only [d3280, d1834, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1834, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3280, d1834, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
