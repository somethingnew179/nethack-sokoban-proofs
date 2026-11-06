/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons146
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c20580 (pattern : Twelve) (guard : d1 pattern = 1) : d1344 pattern ≤ (2 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20579 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20581 (pattern : Twelve) (guard : d1 pattern = 1) : d1348 pattern ≤ (2 : Int) + d1629 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20577 pattern childGuard
    simpa only [d1348, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20580 pattern childGuard
    simpa only [d1348, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20582 (pattern : Twelve) (guard : d1 pattern = 1) : d1350 pattern ≤ (2 : Int) + d1631 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20569 pattern childGuard
    simpa only [d1350, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20581 pattern childGuard
    simpa only [d1350, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20583 (pattern : Twelve) (guard : d1 pattern = 1) : d1351 pattern ≤ (2 : Int) + d1632 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20559 pattern childGuard
    simpa only [d1351, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1351, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20584 (pattern : Twelve) (guard : d1 pattern = 1) : d1352 pattern ≤ (2 : Int) + d1633 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20582 pattern childGuard
    simpa only [d1352, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20583 pattern childGuard
    simpa only [d1352, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20585 (pattern : Twelve) (guard : d1 pattern = 1) : d1353 pattern ≤ (2 : Int) + d1634 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20560 pattern childGuard
    simpa only [d1353, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20584 pattern childGuard
    simpa only [d1353, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20586 (pattern : Twelve) (guard : d0 pattern = 1) : d1634 pattern ≤ (2 : Int) + d1634 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20587 (pattern : Twelve) (guard : d1871 pattern = 1) : d1635 pattern ≤ (2 : Int) + d1634 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20585 pattern childGuard
    simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20586 pattern childGuard
    simpa only [d1871, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20588 (pattern : Twelve) (guard : d1871 pattern = 1) : d1636 pattern ≤ (2 : Int) + d3239 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1636, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20534 pattern childGuard
    simpa only [d1636, d3239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1636, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20587 pattern childGuard
    simpa only [d1636, d3239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20589 (pattern : Twelve) (guard : d1871 pattern = 1) : d1664 pattern ≤ (2 : Int) + d1664 pattern := by
  omega
theorem c20590 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13994 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20466 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20591 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (2 : Int) + d20 pattern := by
  omega
theorem c20592 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20590 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20591 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20593 (pattern : Twelve) (guard : d1 pattern = 1) : d1668 pattern ≤ (2 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13995 pattern childGuard
    simpa only [d1668, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20592 pattern childGuard
    simpa only [d1668, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20594 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (2 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20467 pattern childGuard
    simpa only [d1650, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1650, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20595 (pattern : Twelve) (guard : d1 pattern = 1) : d1671 pattern ≤ (2 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20593 pattern childGuard
    simpa only [d1671, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20594 pattern childGuard
    simpa only [d1671, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20596 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (2 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20556 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20355 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20597 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20590 pattern childGuard
    simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20360 pattern childGuard
    simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20598 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (2 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20590 pattern childGuard
    simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20599 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (2 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20597 pattern childGuard
    simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20598 pattern childGuard
    simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20600 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (2 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20596 pattern childGuard
    simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20599 pattern childGuard
    simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20601 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (2 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20467 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13614 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20602 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (2 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20601 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20468 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20603 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (2 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20602 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20604 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (2 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20600 pattern childGuard
    simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20603 pattern childGuard
    simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20605 (pattern : Twelve) (guard : d1 pattern = 1) : d1674 pattern ≤ (2 : Int) + d1821 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20595 pattern childGuard
    simpa only [d1674, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20604 pattern childGuard
    simpa only [d1674, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20606 (pattern : Twelve) (guard : d1 pattern = 1) : d1665 pattern ≤ (2 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20590 pattern childGuard
    simpa only [d1665, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20299 pattern childGuard
    simpa only [d1665, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20607 (pattern : Twelve) (guard : d1 pattern = 1) : d1666 pattern ≤ (2 : Int) + d1646 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20597 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20606 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20608 (pattern : Twelve) (guard : d1 pattern = 1) : d1669 pattern ≤ (2 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20556 pattern childGuard
    simpa only [d1669, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20607 pattern childGuard
    simpa only [d1669, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20609 (pattern : Twelve) (guard : d1 pattern = 1) : d1672 pattern ≤ (2 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20608 pattern childGuard
    simpa only [d1672, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20603 pattern childGuard
    simpa only [d1672, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20610 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (2 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20360 pattern childGuard
    simpa only [d128, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d128, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20611 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (2 : Int) + d183 pattern := by
  omega
theorem c20612 (pattern : Twelve) (guard : d1 pattern = 1) : d1667 pattern ≤ (2 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20610 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20611 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20613 (pattern : Twelve) (guard : d1 pattern = 1) : d1670 pattern ≤ (2 : Int) + d1817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20602 pattern childGuard
    simpa only [d1670, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20612 pattern childGuard
    simpa only [d1670, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20614 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13614 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20615 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20614 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20616 (pattern : Twelve) (guard : d1 pattern = 1) : d1626 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20615 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20617 (pattern : Twelve) (guard : d1 pattern = 1) : d1673 pattern ≤ (2 : Int) + d1820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20613 pattern childGuard
    simpa only [d1673, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20616 pattern childGuard
    simpa only [d1673, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20618 (pattern : Twelve) (guard : d1 pattern = 1) : d1675 pattern ≤ (2 : Int) + d1822 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20609 pattern childGuard
    simpa only [d1675, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20617 pattern childGuard
    simpa only [d1675, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20619 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (2 : Int) + d1823 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20604 pattern childGuard
    simpa only [d1662, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1662, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20620 (pattern : Twelve) (guard : d1 pattern = 1) : d1676 pattern ≤ (2 : Int) + d1824 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20618 pattern childGuard
    simpa only [d1676, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20619 pattern childGuard
    simpa only [d1676, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20621 (pattern : Twelve) (guard : d1 pattern = 1) : d1677 pattern ≤ (2 : Int) + d1825 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20605 pattern childGuard
    simpa only [d1677, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20620 pattern childGuard
    simpa only [d1677, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20622 (pattern : Twelve) (guard : d0 pattern = 1) : d1825 pattern ≤ (2 : Int) + d1825 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20623 (pattern : Twelve) (guard : d1871 pattern = 1) : d1826 pattern ≤ (2 : Int) + d1825 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20621 pattern childGuard
    simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20622 pattern childGuard
    simpa only [d1871, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20624 (pattern : Twelve) (guard : d1871 pattern = 1) : d1827 pattern ≤ (2 : Int) + d3240 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1827, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20589 pattern childGuard
    simpa only [d1827, d3240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1827, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20623 pattern childGuard
    simpa only [d1827, d3240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20625 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d116 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20626 (pattern : Twelve) (guard : d1878 pattern = 1) : d813 pattern ≤ (2 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10135 pattern childGuard
    simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20625 pattern childGuard
    simpa only [d1878, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20627 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d871 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20628 (pattern : Twelve) (guard : d1878 pattern = 1) : d1274 pattern ≤ (2 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10136 pattern childGuard
    simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20627 pattern childGuard
    simpa only [d1878, d1274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20629 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1323 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20630 (pattern : Twelve) (guard : d1878 pattern = 1) : d1643 pattern ≤ (2 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10137 pattern childGuard
    simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20629 pattern childGuard
    simpa only [d1878, d1643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20631 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1664 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20632 (pattern : Twelve) (guard : d1878 pattern = 1) : d1834 pattern ≤ (2 : Int) + d1664 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10138 pattern childGuard
    simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20631 pattern childGuard
    simpa only [d1878, d1834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20633 (pattern : Twelve) (guard : d1878 pattern = 1) : d116 pattern ≤ (0 : Int) + d116 pattern := by
  omega
theorem c20634 (pattern : Twelve) (guard : d1878 pattern = 1) : d871 pattern ≤ (0 : Int) + d871 pattern := by
  omega
theorem c20635 (pattern : Twelve) (guard : d1878 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1323 pattern := by
  omega
theorem c20636 (pattern : Twelve) (guard : d1878 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1664 pattern := by
  omega
theorem c20637 (pattern : Twelve) (guard : d1873 pattern = 1) : d806 pattern ≤ (2 : Int) + d806 pattern := by
  omega
theorem c20638 (pattern : Twelve) (guard : d1873 pattern = 1) : d1267 pattern ≤ (2 : Int) + d1267 pattern := by
  omega
theorem c20639 (pattern : Twelve) (guard : d1873 pattern = 1) : d1636 pattern ≤ (2 : Int) + d1636 pattern := by
  omega
theorem c20640 (pattern : Twelve) (guard : d1873 pattern = 1) : d1827 pattern ≤ (2 : Int) + d1827 pattern := by
  omega
theorem c20641 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (2 : Int) + d806 pattern := by
  omega
theorem c20642 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (2 : Int) + d1267 pattern := by
  omega
theorem c20643 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (2 : Int) + d1636 pattern := by
  omega
theorem c20644 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (2 : Int) + d1827 pattern := by
  omega
theorem c20645 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (15 : Int) + d0 pattern := by
  omega
theorem c20646 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (15 : Int) + d1 pattern := by
  change (0 : Int) ≤ (15 : Int) + 1
  decide
theorem c20647 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (15 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20645 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20646 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20648 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (15 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20645 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20647 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20649 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (15 : Int) + d1 pattern := by
  omega
theorem c20650 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (15 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20648 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20649 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20651 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (15 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20646 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20649 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20652 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (15 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20647 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20651 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20653 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (15 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20652 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20649 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20654 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (15 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20650 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20653 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20655 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (15 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20645 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20654 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20656 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (15 : Int) + d2 pattern := by
  change (0 : Int) ≤ (15 : Int) + 2
  decide
theorem c20657 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20645 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20656 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20658 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (15 : Int) + d3 pattern := by
  change (1 : Int) ≤ (15 : Int) + 3
  decide
theorem c20659 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (15 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20646 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20658 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20660 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (15 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20657 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20659 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20661 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (15 : Int) + d2 pattern := by
  change (1 : Int) ≤ (15 : Int) + 2
  decide
theorem c20662 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (15 : Int) + d4 pattern := by
  change (2 : Int) ≤ (15 : Int) + 4
  decide
theorem c20663 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (15 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20661 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20662 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20664 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (15 : Int) + d3 pattern := by
  change (2 : Int) ≤ (15 : Int) + 3
  decide
theorem c20665 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (15 : Int) + d5 pattern := by
  change (3 : Int) ≤ (15 : Int) + 5
  decide
theorem c20666 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (15 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20664 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20665 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20667 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (15 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20663 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20666 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20668 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (15 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20660 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20667 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20669 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (15 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20656 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20662 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20670 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (15 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20658 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20665 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20671 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (15 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20669 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20670 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20672 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (15 : Int) + d6 pattern := by
  omega
theorem c20673 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (15 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20671 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20674 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (15 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20668 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20673 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20675 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (15 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20648 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20674 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20676 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (15 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20655 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20675 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20677 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (15 : Int) + d30 pattern := by
  omega
theorem c20678 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (15 : Int) + d6 pattern := by
  change (3 : Int) ≤ (15 : Int) + 6
  decide
theorem c20679 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (15 : Int) + d6 pattern := by
  change (5 : Int) ≤ (15 : Int) + 6
  decide
theorem c20680 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20678 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20679 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20681 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (15 : Int) + d6 pattern := by
  change (4 : Int) ≤ (15 : Int) + 6
  decide
theorem c20682 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20681 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20683 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20680 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20682 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20684 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (15 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20645 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20683 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20685 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (15 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20677 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20684 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20686 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (15 : Int) + d2 pattern := by
  omega
theorem c20687 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (15 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20686 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20664 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20688 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (15 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20686 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20687 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20689 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (15 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20648 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20688 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20690 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20679 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20691 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20682 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20690 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20692 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (15 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20652 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20691 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20693 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (15 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20692 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20694 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (15 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20685 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20693 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20695 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20690 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20696 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (15 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20648 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20695 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20697 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (15 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20696 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20698 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (15 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20686 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20662 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20699 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (15 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20698 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20666 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20700 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (15 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20660 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20699 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20701 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (15 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20700 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20673 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20702 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (15 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20697 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20701 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20703 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (15 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20694 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20702 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20704 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (15 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20676 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20703 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20705 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (15 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20648 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20701 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20706 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (15 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20655 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20705 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20707 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (15 : Int) + d56 pattern := by
  omega
theorem c20708 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (15 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20652 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20709 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (15 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20708 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20710 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (15 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20707 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20709 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20711 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (15 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20648 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20712 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (15 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20711 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20713 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (15 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20712 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20701 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20714 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (15 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20710 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20713 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20715 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (15 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20706 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20714 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20716 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (15 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20704 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20715 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20717 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (15 : Int) + d3 pattern := by
  omega
theorem c20718 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (15 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20652 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20717 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20719 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (15 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20718 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
