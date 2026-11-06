/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons067
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c9520 (pattern : Twelve) (guard : d1848 pattern = 1) : d1329 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1329, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1329, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1329, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9519 pattern childGuard
    simpa only [d1848, d1329, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9521 (pattern : Twelve) (guard : d1848 pattern = 1) : d1336 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1991 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9520 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9522 (pattern : Twelve) (guard : d1848 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1342, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9521 pattern childGuard
    simpa only [d1342, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1342, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1342, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9523 (pattern : Twelve) (guard : d1848 pattern = 1) : d1347 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1347, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9503 pattern childGuard
    simpa only [d1347, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1347, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9522 pattern childGuard
    simpa only [d1347, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9524 (pattern : Twelve) (guard : d1869 pattern = 1) : d1350 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1350, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9523 pattern childGuard
    simpa only [d1869, d1350, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1350, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9509 pattern childGuard
    simpa only [d1869, d1350, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9525 (pattern : Twelve) (guard : d1848 pattern = 1) : d1346 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1346, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9512 pattern childGuard
    simpa only [d1346, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1346, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9482 pattern childGuard
    simpa only [d1346, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9526 (pattern : Twelve) (guard : d1869 pattern = 1) : d1351 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1351, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9525 pattern childGuard
    simpa only [d1869, d1351, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1351, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1351, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9527 (pattern : Twelve) (guard : d1869 pattern = 1) : d1352 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9524 pattern childGuard
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9526 pattern childGuard
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9528 (pattern : Twelve) (guard : d1869 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9518 pattern childGuard
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9527 pattern childGuard
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9529 (pattern : Twelve) (guard : d1869 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9516 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9528 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9530 (pattern : Twelve) (guard : d1869 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1443 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1354, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9490 pattern childGuard
    simpa only [d1354, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1354, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9529 pattern childGuard
    simpa only [d1354, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9531 (pattern : Twelve) (guard : d1869 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1660, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4852 pattern childGuard
    simpa only [d1869, d1660, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1660, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c804 pattern childGuard
    simpa only [d1869, d1660, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9532 (pattern : Twelve) (guard : d1848 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1976 pattern childGuard
    simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2012 pattern childGuard
    simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9533 (pattern : Twelve) (guard : d1848 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2016 pattern childGuard
    simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9534 (pattern : Twelve) (guard : d1848 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9532 pattern childGuard
    simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9533 pattern childGuard
    simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9535 (pattern : Twelve) (guard : d0 pattern = 1) : d1659 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9536 (pattern : Twelve) (guard : d1869 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1661, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9534 pattern childGuard
    simpa only [d1869, d1661, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1661, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9535 pattern childGuard
    simpa only [d1869, d1661, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9537 (pattern : Twelve) (guard : d1848 pattern = 1) : d1647 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2012 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5211 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9538 (pattern : Twelve) (guard : d1848 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9469 pattern childGuard
    simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9537 pattern childGuard
    simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9539 (pattern : Twelve) (guard : d1848 pattern = 1) : d1289 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2016 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5214 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9540 (pattern : Twelve) (guard : d1848 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9539 pattern childGuard
    simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9541 (pattern : Twelve) (guard : d1848 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9538 pattern childGuard
    simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9540 pattern childGuard
    simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9542 (pattern : Twelve) (guard : d1869 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1662, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9541 pattern childGuard
    simpa only [d1869, d1662, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1662, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1662, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9543 (pattern : Twelve) (guard : d1869 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9536 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9542 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9544 (pattern : Twelve) (guard : d1869 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9531 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9543 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9545 (pattern : Twelve) (guard : d1848 pattern = 1) : d1668 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1741 pattern childGuard
    simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2012 pattern childGuard
    simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9546 (pattern : Twelve) (guard : d1848 pattern = 1) : d1671 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9545 pattern childGuard
    simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4868 pattern childGuard
    simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9547 (pattern : Twelve) (guard : d1869 pattern = 1) : d1674 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1674, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9546 pattern childGuard
    simpa only [d1869, d1674, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1674, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c804 pattern childGuard
    simpa only [d1869, d1674, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9548 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9549 (pattern : Twelve) (guard : d1848 pattern = 1) : d1665 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9548 pattern childGuard
    simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9550 (pattern : Twelve) (guard : d1848 pattern = 1) : d1666 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2012 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9549 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9551 (pattern : Twelve) (guard : d1848 pattern = 1) : d1669 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1669, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1976 pattern childGuard
    simpa only [d1669, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1669, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9550 pattern childGuard
    simpa only [d1669, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9552 (pattern : Twelve) (guard : d1848 pattern = 1) : d1672 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1672, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9551 pattern childGuard
    simpa only [d1672, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1672, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9540 pattern childGuard
    simpa only [d1672, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9553 (pattern : Twelve) (guard : d0 pattern = 1) : d1673 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9554 (pattern : Twelve) (guard : d1869 pattern = 1) : d1675 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1675, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9552 pattern childGuard
    simpa only [d1869, d1675, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1675, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9553 pattern childGuard
    simpa only [d1869, d1675, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9555 (pattern : Twelve) (guard : d1869 pattern = 1) : d1676 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9554 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9542 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9556 (pattern : Twelve) (guard : d1869 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9547 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9555 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9557 (pattern : Twelve) (guard : d1869 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9544 pattern childGuard
    simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9556 pattern childGuard
    simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9558 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (0 : Int) + d114 pattern := by
  omega
theorem c9559 (pattern : Twelve) (guard : d0 pattern = 1) : d114 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9560 (pattern : Twelve) (guard : d1871 pattern = 1) : d114 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9558 pattern childGuard
    simpa only [d1871, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9559 pattern childGuard
    simpa only [d1871, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9561 (pattern : Twelve) (guard : d1 pattern = 1) : d155 pattern ≤ (0 : Int) + d155 pattern := by
  omega
theorem c9562 (pattern : Twelve) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9563 (pattern : Twelve) (guard : d1871 pattern = 1) : d155 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9561 pattern childGuard
    simpa only [d1871, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9562 pattern childGuard
    simpa only [d1871, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9564 (pattern : Twelve) (guard : d1871 pattern = 1) : d156 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d156, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9560 pattern childGuard
    simpa only [d156, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d156, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9563 pattern childGuard
    simpa only [d156, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9565 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (0 : Int) + d869 pattern := by
  omega
theorem c9566 (pattern : Twelve) (guard : d0 pattern = 1) : d869 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9567 (pattern : Twelve) (guard : d1871 pattern = 1) : d869 pattern ≤ (0 : Int) + d1268 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9565 pattern childGuard
    simpa only [d1871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9566 pattern childGuard
    simpa only [d1871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9568 (pattern : Twelve) (guard : d1 pattern = 1) : d906 pattern ≤ (0 : Int) + d906 pattern := by
  omega
theorem c9569 (pattern : Twelve) (guard : d0 pattern = 1) : d906 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9570 (pattern : Twelve) (guard : d1871 pattern = 1) : d906 pattern ≤ (0 : Int) + d1269 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9568 pattern childGuard
    simpa only [d1871, d1269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9569 pattern childGuard
    simpa only [d1871, d1269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9571 (pattern : Twelve) (guard : d1871 pattern = 1) : d907 pattern ≤ (0 : Int) + d1270 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d907, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9567 pattern childGuard
    simpa only [d907, d1270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d907, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9570 pattern childGuard
    simpa only [d907, d1270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9572 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1321 pattern := by
  omega
theorem c9573 (pattern : Twelve) (guard : d0 pattern = 1) : d1321 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9574 (pattern : Twelve) (guard : d1871 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1637 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9572 pattern childGuard
    simpa only [d1871, d1637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9573 pattern childGuard
    simpa only [d1871, d1637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9575 (pattern : Twelve) (guard : d1 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1353 pattern := by
  omega
theorem c9576 (pattern : Twelve) (guard : d0 pattern = 1) : d1353 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9577 (pattern : Twelve) (guard : d1871 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1638 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9575 pattern childGuard
    simpa only [d1871, d1638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9576 pattern childGuard
    simpa only [d1871, d1638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9578 (pattern : Twelve) (guard : d1871 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1639 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1354, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9574 pattern childGuard
    simpa only [d1354, d1639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1354, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9577 pattern childGuard
    simpa only [d1354, d1639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9579 (pattern : Twelve) (guard : d0 pattern = 1) : d1664 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9580 (pattern : Twelve) (guard : d1871 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1828 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1871, d1828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9579 pattern childGuard
    simpa only [d1871, d1828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9581 (pattern : Twelve) (guard : d1 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1677 pattern := by
  omega
theorem c9582 (pattern : Twelve) (guard : d0 pattern = 1) : d1677 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9583 (pattern : Twelve) (guard : d1871 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1829 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9581 pattern childGuard
    simpa only [d1871, d1829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9582 pattern childGuard
    simpa only [d1871, d1829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9584 (pattern : Twelve) (guard : d1871 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1830 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1678, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9580 pattern childGuard
    simpa only [d1678, d1830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1678, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9583 pattern childGuard
    simpa only [d1678, d1830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9585 (pattern : Twelve) (guard : d0 pattern = 1) : d114 pattern ≤ (0 : Int) + d115 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9586 (pattern : Twelve) (guard : d1871 pattern = 1) : d114 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9558 pattern childGuard
    simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9585 pattern childGuard
    simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9587 (pattern : Twelve) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d804 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9588 (pattern : Twelve) (guard : d1871 pattern = 1) : d155 pattern ≤ (0 : Int) + d805 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9561 pattern childGuard
    simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9587 pattern childGuard
    simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9589 (pattern : Twelve) (guard : d1871 pattern = 1) : d156 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d156, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9586 pattern childGuard
    simpa only [d156, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d156, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9588 pattern childGuard
    simpa only [d156, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9590 (pattern : Twelve) (guard : d0 pattern = 1) : d869 pattern ≤ (0 : Int) + d870 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9591 (pattern : Twelve) (guard : d1871 pattern = 1) : d869 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9565 pattern childGuard
    simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9590 pattern childGuard
    simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9592 (pattern : Twelve) (guard : d0 pattern = 1) : d906 pattern ≤ (0 : Int) + d1265 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9593 (pattern : Twelve) (guard : d1871 pattern = 1) : d906 pattern ≤ (0 : Int) + d1266 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9568 pattern childGuard
    simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9592 pattern childGuard
    simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9594 (pattern : Twelve) (guard : d1871 pattern = 1) : d907 pattern ≤ (0 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d907, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9591 pattern childGuard
    simpa only [d907, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d907, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9593 pattern childGuard
    simpa only [d907, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9595 (pattern : Twelve) (guard : d0 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1322 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9596 (pattern : Twelve) (guard : d1871 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9572 pattern childGuard
    simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9595 pattern childGuard
    simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9597 (pattern : Twelve) (guard : d0 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1634 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9598 (pattern : Twelve) (guard : d1871 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1635 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9575 pattern childGuard
    simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9597 pattern childGuard
    simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9599 (pattern : Twelve) (guard : d1871 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1354, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9596 pattern childGuard
    simpa only [d1354, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1354, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9598 pattern childGuard
    simpa only [d1354, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9600 (pattern : Twelve) (guard : d1871 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1664 pattern := by
  omega
theorem c9601 (pattern : Twelve) (guard : d0 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1825 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9602 (pattern : Twelve) (guard : d1871 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1826 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9581 pattern childGuard
    simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9601 pattern childGuard
    simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9603 (pattern : Twelve) (guard : d1871 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1678, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9600 pattern childGuard
    simpa only [d1678, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1678, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9602 pattern childGuard
    simpa only [d1678, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9604 (pattern : Twelve) (guard : d0 pattern = 1) : d156 pattern ≤ (0 : Int) + d116 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9605 (pattern : Twelve) (guard : d0 pattern = 1) : d907 pattern ≤ (0 : Int) + d871 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9606 (pattern : Twelve) (guard : d0 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1323 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9607 (pattern : Twelve) (guard : d0 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1664 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9608 (pattern : Twelve) (guard : d0 pattern = 1) : d115 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9609 (pattern : Twelve) (guard : d1871 pattern = 1) : d116 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d116, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9558 pattern childGuard
    simpa only [d1871, d116, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d116, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9608 pattern childGuard
    simpa only [d1871, d116, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9610 (pattern : Twelve) (guard : d0 pattern = 1) : d804 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9611 (pattern : Twelve) (guard : d1871 pattern = 1) : d805 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d805, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9561 pattern childGuard
    simpa only [d1871, d805, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d805, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9610 pattern childGuard
    simpa only [d1871, d805, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9612 (pattern : Twelve) (guard : d1871 pattern = 1) : d806 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d806, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9609 pattern childGuard
    simpa only [d806, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d806, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9611 pattern childGuard
    simpa only [d806, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9613 (pattern : Twelve) (guard : d0 pattern = 1) : d870 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9614 (pattern : Twelve) (guard : d1871 pattern = 1) : d871 pattern ≤ (0 : Int) + d1268 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9565 pattern childGuard
    simpa only [d1871, d871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9613 pattern childGuard
    simpa only [d1871, d871, d1268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9615 (pattern : Twelve) (guard : d0 pattern = 1) : d1265 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9616 (pattern : Twelve) (guard : d1871 pattern = 1) : d1266 pattern ≤ (0 : Int) + d1269 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1266, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9568 pattern childGuard
    simpa only [d1871, d1266, d1269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1266, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9615 pattern childGuard
    simpa only [d1871, d1266, d1269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9617 (pattern : Twelve) (guard : d1871 pattern = 1) : d1267 pattern ≤ (0 : Int) + d1270 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1267, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9614 pattern childGuard
    simpa only [d1267, d1270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1267, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9616 pattern childGuard
    simpa only [d1267, d1270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9618 (pattern : Twelve) (guard : d0 pattern = 1) : d1322 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9619 (pattern : Twelve) (guard : d1871 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1637 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1323, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9572 pattern childGuard
    simpa only [d1871, d1323, d1637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1323, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9618 pattern childGuard
    simpa only [d1871, d1323, d1637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9620 (pattern : Twelve) (guard : d0 pattern = 1) : d1634 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9621 (pattern : Twelve) (guard : d1871 pattern = 1) : d1635 pattern ≤ (0 : Int) + d1638 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1635, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9575 pattern childGuard
    simpa only [d1871, d1635, d1638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1635, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9620 pattern childGuard
    simpa only [d1871, d1635, d1638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9622 (pattern : Twelve) (guard : d1871 pattern = 1) : d1636 pattern ≤ (0 : Int) + d1639 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1636, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9619 pattern childGuard
    simpa only [d1636, d1639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1636, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9621 pattern childGuard
    simpa only [d1636, d1639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9623 (pattern : Twelve) (guard : d0 pattern = 1) : d1825 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9624 (pattern : Twelve) (guard : d1871 pattern = 1) : d1826 pattern ≤ (0 : Int) + d1829 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1826, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9581 pattern childGuard
    simpa only [d1871, d1826, d1829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1826, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9623 pattern childGuard
    simpa only [d1871, d1826, d1829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9625 (pattern : Twelve) (guard : d1871 pattern = 1) : d1827 pattern ≤ (0 : Int) + d1830 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1827, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9580 pattern childGuard
    simpa only [d1827, d1830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1827, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9624 pattern childGuard
    simpa only [d1827, d1830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9626 (pattern : Twelve) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9627 (pattern : Twelve) (guard : d1873 pattern = 1) : d116 pattern ≤ (0 : Int) + d810 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c0 pattern childGuard
    simpa only [d1873, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9626 pattern childGuard
    simpa only [d1873, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9628 (pattern : Twelve) (guard : d1 pattern = 1) : d805 pattern ≤ (0 : Int) + d805 pattern := by
  omega
theorem c9629 (pattern : Twelve) (guard : d0 pattern = 1) : d805 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9630 (pattern : Twelve) (guard : d1873 pattern = 1) : d805 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9628 pattern childGuard
    simpa only [d1873, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9629 pattern childGuard
    simpa only [d1873, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9631 (pattern : Twelve) (guard : d1873 pattern = 1) : d806 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1873 pattern = 1 := by simpa only [d806, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9627 pattern childGuard
    simpa only [d806, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1873 pattern = 1 := by simpa only [d806, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9630 pattern childGuard
    simpa only [d806, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9632 (pattern : Twelve) (guard : d0 pattern = 1) : d871 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9633 (pattern : Twelve) (guard : d1873 pattern = 1) : d871 pattern ≤ (0 : Int) + d1271 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1 pattern childGuard
    simpa only [d1873, d1271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9632 pattern childGuard
    simpa only [d1873, d1271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9634 (pattern : Twelve) (guard : d1 pattern = 1) : d1266 pattern ≤ (0 : Int) + d1266 pattern := by
  omega
theorem c9635 (pattern : Twelve) (guard : d0 pattern = 1) : d1266 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9636 (pattern : Twelve) (guard : d1873 pattern = 1) : d1266 pattern ≤ (0 : Int) + d1272 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9634 pattern childGuard
    simpa only [d1873, d1272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9635 pattern childGuard
    simpa only [d1873, d1272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9637 (pattern : Twelve) (guard : d1873 pattern = 1) : d1267 pattern ≤ (0 : Int) + d1273 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1267, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9633 pattern childGuard
    simpa only [d1267, d1273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1267, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9636 pattern childGuard
    simpa only [d1267, d1273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9638 (pattern : Twelve) (guard : d0 pattern = 1) : d1323 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9639 (pattern : Twelve) (guard : d1873 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1640 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d1873, d1640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9638 pattern childGuard
    simpa only [d1873, d1640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9640 (pattern : Twelve) (guard : d1 pattern = 1) : d1635 pattern ≤ (0 : Int) + d1635 pattern := by
  omega
theorem c9641 (pattern : Twelve) (guard : d0 pattern = 1) : d1635 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9642 (pattern : Twelve) (guard : d1873 pattern = 1) : d1635 pattern ≤ (0 : Int) + d1641 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9640 pattern childGuard
    simpa only [d1873, d1641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9641 pattern childGuard
    simpa only [d1873, d1641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9643 (pattern : Twelve) (guard : d1873 pattern = 1) : d1636 pattern ≤ (0 : Int) + d1642 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1636, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9639 pattern childGuard
    simpa only [d1636, d1642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1636, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9642 pattern childGuard
    simpa only [d1636, d1642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9644 (pattern : Twelve) (guard : d1873 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1831 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1873, d1831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9579 pattern childGuard
    simpa only [d1873, d1831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9645 (pattern : Twelve) (guard : d1 pattern = 1) : d1826 pattern ≤ (0 : Int) + d1826 pattern := by
  omega
theorem c9646 (pattern : Twelve) (guard : d0 pattern = 1) : d1826 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9647 (pattern : Twelve) (guard : d1873 pattern = 1) : d1826 pattern ≤ (0 : Int) + d1832 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1873, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9645 pattern childGuard
    simpa only [d1873, d1832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1873, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9646 pattern childGuard
    simpa only [d1873, d1832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9648 (pattern : Twelve) (guard : d1873 pattern = 1) : d1827 pattern ≤ (0 : Int) + d1833 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1827, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9644 pattern childGuard
    simpa only [d1827, d1833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1873 pattern = 1 := by simpa only [d1827, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9647 pattern childGuard
    simpa only [d1827, d1833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9649 (pattern : Twelve) (guard : d0 pattern = 1) : d115 pattern ≤ (0 : Int) + d114 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9650 (pattern : Twelve) (guard : d1871 pattern = 1) : d116 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9558 pattern childGuard
    simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9649 pattern childGuard
    simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9651 (pattern : Twelve) (guard : d0 pattern = 1) : d804 pattern ≤ (0 : Int) + d155 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9652 (pattern : Twelve) (guard : d1871 pattern = 1) : d805 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9561 pattern childGuard
    simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9651 pattern childGuard
    simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9653 (pattern : Twelve) (guard : d1871 pattern = 1) : d806 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d806, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9650 pattern childGuard
    simpa only [d806, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d806, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9652 pattern childGuard
    simpa only [d806, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9654 (pattern : Twelve) (guard : d0 pattern = 1) : d870 pattern ≤ (0 : Int) + d869 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9655 (pattern : Twelve) (guard : d1871 pattern = 1) : d871 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9565 pattern childGuard
    simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9654 pattern childGuard
    simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9656 (pattern : Twelve) (guard : d0 pattern = 1) : d1265 pattern ≤ (0 : Int) + d906 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9657 (pattern : Twelve) (guard : d1871 pattern = 1) : d1266 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9568 pattern childGuard
    simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9656 pattern childGuard
    simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9658 (pattern : Twelve) (guard : d1871 pattern = 1) : d1267 pattern ≤ (0 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1267, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9655 pattern childGuard
    simpa only [d1267, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1267, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9657 pattern childGuard
    simpa only [d1267, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9659 (pattern : Twelve) (guard : d0 pattern = 1) : d1322 pattern ≤ (0 : Int) + d1321 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
