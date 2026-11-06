/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons160
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c22540 (pattern : Twelve) (guard : d1 pattern = 1) : d1624 pattern ≤ (19 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22168 pattern childGuard
    simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22539 pattern childGuard
    simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22541 (pattern : Twelve) (guard : d1 pattern = 1) : d1628 pattern ≤ (19 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22540 pattern childGuard
    simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22494 pattern childGuard
    simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22542 (pattern : Twelve) (guard : d1 pattern = 1) : d182 pattern ≤ (19 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22255 pattern childGuard
    simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22543 (pattern : Twelve) (guard : d1 pattern = 1) : d1621 pattern ≤ (19 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22520 pattern childGuard
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22542 pattern childGuard
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22544 (pattern : Twelve) (guard : d1 pattern = 1) : d1625 pattern ≤ (19 : Int) + d1817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22214 pattern childGuard
    simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22543 pattern childGuard
    simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22545 (pattern : Twelve) (guard : d1 pattern = 1) : d1626 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22441 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22546 (pattern : Twelve) (guard : d1 pattern = 1) : d1629 pattern ≤ (19 : Int) + d1820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22544 pattern childGuard
    simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22545 pattern childGuard
    simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22547 (pattern : Twelve) (guard : d1 pattern = 1) : d1631 pattern ≤ (19 : Int) + d1822 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22541 pattern childGuard
    simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22546 pattern childGuard
    simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22548 (pattern : Twelve) (guard : d1 pattern = 1) : d1632 pattern ≤ (19 : Int) + d1823 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22495 pattern childGuard
    simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22549 (pattern : Twelve) (guard : d1 pattern = 1) : d1633 pattern ≤ (19 : Int) + d1824 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22547 pattern childGuard
    simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22548 pattern childGuard
    simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22550 (pattern : Twelve) (guard : d1 pattern = 1) : d1634 pattern ≤ (19 : Int) + d1825 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22537 pattern childGuard
    simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22549 pattern childGuard
    simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22551 (pattern : Twelve) (guard : d1 pattern = 1) : d1635 pattern ≤ (19 : Int) + d1826 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22530 pattern childGuard
    simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22550 pattern childGuard
    simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22552 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (19 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22500 pattern childGuard
    simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22551 pattern childGuard
    simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22553 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22317 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22319 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22554 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22318 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22553 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22555 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22320 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22556 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22554 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22555 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22557 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22318 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22558 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22321 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22557 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22559 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22553 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22112 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22560 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22553 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22561 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22559 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22560 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22562 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22558 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22561 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22563 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22349 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22322 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22564 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22563 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22565 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22562 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22564 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22566 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22556 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22565 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22567 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22321 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22559 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22568 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22349 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22569 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22567 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22568 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22570 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22112 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22124 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22571 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22570 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22267 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22572 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22563 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22571 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22573 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22350 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22574 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22572 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22573 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22575 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22569 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22574 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22576 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22565 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22577 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22575 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22576 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22578 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22566 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22577 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22579 (pattern : Twelve) (guard : d1 pattern = 1) : d1668 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22318 pattern childGuard
    simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22559 pattern childGuard
    simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22580 (pattern : Twelve) (guard : d1 pattern = 1) : d1671 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22579 pattern childGuard
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22555 pattern childGuard
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22581 (pattern : Twelve) (guard : d1 pattern = 1) : d1674 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22580 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22565 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22582 (pattern : Twelve) (guard : d1 pattern = 1) : d1665 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22553 pattern childGuard
    simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22124 pattern childGuard
    simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22583 (pattern : Twelve) (guard : d1 pattern = 1) : d1666 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22559 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22582 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22584 (pattern : Twelve) (guard : d1 pattern = 1) : d1669 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22321 pattern childGuard
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22583 pattern childGuard
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22585 (pattern : Twelve) (guard : d1 pattern = 1) : d1672 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22584 pattern childGuard
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22564 pattern childGuard
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22586 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22124 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22587 (pattern : Twelve) (guard : d1 pattern = 1) : d1667 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22267 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22586 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22588 (pattern : Twelve) (guard : d1 pattern = 1) : d1670 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22563 pattern childGuard
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22587 pattern childGuard
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22589 (pattern : Twelve) (guard : d1 pattern = 1) : d1673 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22588 pattern childGuard
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22545 pattern childGuard
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22590 (pattern : Twelve) (guard : d1 pattern = 1) : d1675 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22585 pattern childGuard
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22589 pattern childGuard
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22591 (pattern : Twelve) (guard : d1 pattern = 1) : d1676 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22590 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22576 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22592 (pattern : Twelve) (guard : d1 pattern = 1) : d1677 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22581 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22591 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22593 (pattern : Twelve) (guard : d1 pattern = 1) : d1814 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22320 pattern childGuard
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22112 pattern childGuard
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22594 (pattern : Twelve) (guard : d1 pattern = 1) : d1815 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22120 pattern childGuard
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22595 (pattern : Twelve) (guard : d1 pattern = 1) : d1818 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22593 pattern childGuard
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22594 pattern childGuard
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22596 (pattern : Twelve) (guard : d1 pattern = 1) : d1821 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22595 pattern childGuard
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22574 pattern childGuard
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22597 (pattern : Twelve) (guard : d1 pattern = 1) : d1816 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22349 pattern childGuard
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22570 pattern childGuard
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22598 (pattern : Twelve) (guard : d1 pattern = 1) : d1819 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22597 pattern childGuard
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22573 pattern childGuard
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22599 (pattern : Twelve) (guard : d1 pattern = 1) : d1817 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22350 pattern childGuard
    simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22586 pattern childGuard
    simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22600 (pattern : Twelve) (guard : d1 pattern = 1) : d1820 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22599 pattern childGuard
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22601 (pattern : Twelve) (guard : d1 pattern = 1) : d1822 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22598 pattern childGuard
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22600 pattern childGuard
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22602 (pattern : Twelve) (guard : d1 pattern = 1) : d1823 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22574 pattern childGuard
    simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22603 (pattern : Twelve) (guard : d1 pattern = 1) : d1824 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22601 pattern childGuard
    simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22602 pattern childGuard
    simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22604 (pattern : Twelve) (guard : d1 pattern = 1) : d1825 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22596 pattern childGuard
    simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22603 pattern childGuard
    simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22605 (pattern : Twelve) (guard : d1 pattern = 1) : d1826 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22592 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22604 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22606 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22578 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22605 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22607 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (3 : Int) + d806 pattern := by
  omega
theorem c22608 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (3 : Int) + d1267 pattern := by
  omega
theorem c22609 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (3 : Int) + d1636 pattern := by
  omega
theorem c22610 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (3 : Int) + d1827 pattern := by
  omega
theorem c22611 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (4 : Int) + d806 pattern := by
  omega
theorem c22612 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (4 : Int) + d1267 pattern := by
  omega
theorem c22613 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (4 : Int) + d1636 pattern := by
  omega
theorem c22614 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (4 : Int) + d1827 pattern := by
  omega
theorem c22615 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (5 : Int) + d72 pattern := by
  omega
theorem c22616 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (5 : Int) + d17 pattern := by
  omega
theorem c22617 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (5 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12983 pattern childGuard
    simpa only [d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22618 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (5 : Int) + d29 pattern := by
  omega
theorem c22619 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (5 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22617 pattern childGuard
    simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22618 pattern childGuard
    simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22620 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (5 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22619 pattern childGuard
    simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22621 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (5 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22615 pattern childGuard
    simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22620 pattern childGuard
    simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22622 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (5 : Int) + d52 pattern := by
  omega
theorem c22623 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (5 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13004 pattern childGuard
    simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22624 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (5 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13007 pattern childGuard
    simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22625 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (5 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22623 pattern childGuard
    simpa only [d53, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22624 pattern childGuard
    simpa only [d53, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22626 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (5 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22622 pattern childGuard
    simpa only [d74, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22625 pattern childGuard
    simpa only [d74, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22627 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (5 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13011 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22628 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (5 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12993 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22627 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22629 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (5 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13015 pattern childGuard
    simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22630 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (5 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22629 pattern childGuard
    simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22618 pattern childGuard
    simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22631 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (5 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22628 pattern childGuard
    simpa only [d75, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22630 pattern childGuard
    simpa only [d75, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22632 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (5 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22626 pattern childGuard
    simpa only [d92, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22631 pattern childGuard
    simpa only [d92, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22633 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (5 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22621 pattern childGuard
    simpa only [d102, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22632 pattern childGuard
    simpa only [d102, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22634 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (5 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22630 pattern childGuard
    simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22635 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (5 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22615 pattern childGuard
    simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22634 pattern childGuard
    simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22636 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (5 : Int) + d36 pattern := by
  omega
theorem c22637 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (5 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22623 pattern childGuard
    simpa only [d57, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22636 pattern childGuard
    simpa only [d57, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22638 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (5 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13023 pattern childGuard
    simpa only [d77, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22637 pattern childGuard
    simpa only [d77, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22639 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (5 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13023 pattern childGuard
    simpa only [d78, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22630 pattern childGuard
    simpa only [d78, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22640 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (5 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22638 pattern childGuard
    simpa only [d94, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22639 pattern childGuard
    simpa only [d94, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22641 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (5 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22635 pattern childGuard
    simpa only [d103, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22640 pattern childGuard
    simpa only [d103, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22642 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (5 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22633 pattern childGuard
    simpa only [d110, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22641 pattern childGuard
    simpa only [d110, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22643 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (5 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13132 pattern childGuard
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22644 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (5 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22623 pattern childGuard
    simpa only [d58, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22643 pattern childGuard
    simpa only [d58, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22645 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (5 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12993 pattern childGuard
    simpa only [d79, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22644 pattern childGuard
    simpa only [d79, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22646 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (5 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12980 pattern childGuard
    simpa only [d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22647 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (5 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12993 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22646 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22648 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (5 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22647 pattern childGuard
    simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22630 pattern childGuard
    simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22649 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (5 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22645 pattern childGuard
    simpa only [d95, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22648 pattern childGuard
    simpa only [d95, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22650 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (5 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13041 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22651 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (5 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13041 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22650 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22652 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (5 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13002 pattern childGuard
    simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22651 pattern childGuard
    simpa only [d38, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22653 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (5 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12980 pattern childGuard
    simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13133 pattern childGuard
    simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22654 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (5 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22653 pattern childGuard
    simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d40, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22655 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (5 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22652 pattern childGuard
    simpa only [d60, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22654 pattern childGuard
    simpa only [d60, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22656 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (5 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13039 pattern childGuard
    simpa only [d81, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22655 pattern childGuard
    simpa only [d81, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22657 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (5 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13002 pattern childGuard
    simpa only [d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13041 pattern childGuard
    simpa only [d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22658 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (5 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12980 pattern childGuard
    simpa only [d39, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d39, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22659 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (5 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22657 pattern childGuard
    simpa only [d59, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22658 pattern childGuard
    simpa only [d59, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22660 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (5 : Int) + d23 pattern := by
  omega
theorem c22661 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12995 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22662 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (5 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22650 pattern childGuard
    simpa only [d24, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22661 pattern childGuard
    simpa only [d24, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22663 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (5 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22660 pattern childGuard
    simpa only [d41, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22662 pattern childGuard
    simpa only [d41, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22664 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (5 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12980 pattern childGuard
    simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13041 pattern childGuard
    simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22665 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (5 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13132 pattern childGuard
    simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12995 pattern childGuard
    simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22666 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (5 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22664 pattern childGuard
    simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22665 pattern childGuard
    simpa only [d25, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22667 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (5 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22666 pattern childGuard
    simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d42, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22668 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (5 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22663 pattern childGuard
    simpa only [d61, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22667 pattern childGuard
    simpa only [d61, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22669 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (5 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22659 pattern childGuard
    simpa only [d82, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22668 pattern childGuard
    simpa only [d82, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22670 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (5 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22656 pattern childGuard
    simpa only [d96, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22669 pattern childGuard
    simpa only [d96, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22671 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (5 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22649 pattern childGuard
    simpa only [d104, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22670 pattern childGuard
    simpa only [d104, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22672 (pattern : Twelve) (guard : d1 pattern = 1) : d105 pattern ≤ (5 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22640 pattern childGuard
    simpa only [d105, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d105, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22673 (pattern : Twelve) (guard : d1 pattern = 1) : d111 pattern ≤ (5 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22671 pattern childGuard
    simpa only [d111, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22672 pattern childGuard
    simpa only [d111, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22674 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (5 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22642 pattern childGuard
    simpa only [d114, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22673 pattern childGuard
    simpa only [d114, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22675 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (5 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22676 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (5 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22677 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (5 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22676 pattern childGuard
    simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22678 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (5 : Int) + d779 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22677 pattern childGuard
    simpa only [d27, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d27, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22679 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (5 : Int) + d782 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22675 pattern childGuard
    simpa only [d50, d782, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22678 pattern childGuard
    simpa only [d50, d782, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
