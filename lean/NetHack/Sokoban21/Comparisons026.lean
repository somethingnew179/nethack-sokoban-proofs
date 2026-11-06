/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons025
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c3640 (pattern : Twelve) (guard : d1867 pattern = 1) : d1647 pattern ≤ (0 : Int) + d1784 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1647, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3638 pattern childGuard
    simpa only [d1647, d1784, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1647, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3639 pattern childGuard
    simpa only [d1647, d1784, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3641 (pattern : Twelve) (guard : d1867 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1790 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1651, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3574 pattern childGuard
    simpa only [d1651, d1790, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1651, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3640 pattern childGuard
    simpa only [d1651, d1790, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3642 (pattern : Twelve) (guard : d1867 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1798 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1657, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3641 pattern childGuard
    simpa only [d1657, d1798, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1657, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3593 pattern childGuard
    simpa only [d1657, d1798, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3643 (pattern : Twelve) (guard : d1867 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1804 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1660, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3637 pattern childGuard
    simpa only [d1660, d1804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1660, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3642 pattern childGuard
    simpa only [d1660, d1804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3644 (pattern : Twelve) (guard : d1867 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1791 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1652, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3475 pattern childGuard
    simpa only [d1652, d1791, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1652, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3638 pattern childGuard
    simpa only [d1652, d1791, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3645 (pattern : Twelve) (guard : d1867 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1792 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1653, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3506 pattern childGuard
    simpa only [d1653, d1792, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1653, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1653, d1792, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3646 (pattern : Twelve) (guard : d1867 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1799 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1658, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3644 pattern childGuard
    simpa only [d1658, d1799, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1658, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3645 pattern childGuard
    simpa only [d1658, d1799, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3647 (pattern : Twelve) (guard : d1867 pattern = 1) : d1646 pattern ≤ (0 : Int) + d1782 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1646, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3291 pattern childGuard
    simpa only [d1646, d1782, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1646, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1646, d1782, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3648 (pattern : Twelve) (guard : d1867 pattern = 1) : d1648 pattern ≤ (0 : Int) + d1785 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1648, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3647 pattern childGuard
    simpa only [d1648, d1785, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1648, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3459 pattern childGuard
    simpa only [d1648, d1785, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3649 (pattern : Twelve) (guard : d1867 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1793 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1654, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3592 pattern childGuard
    simpa only [d1654, d1793, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1654, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3648 pattern childGuard
    simpa only [d1654, d1793, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3650 (pattern : Twelve) (guard : d1867 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1655 pattern := by
  omega
theorem c3651 (pattern : Twelve) (guard : d1867 pattern = 1) : d1659 pattern ≤ (0 : Int) + d1800 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1659, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3649 pattern childGuard
    simpa only [d1659, d1800, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1659, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3650 pattern childGuard
    simpa only [d1659, d1800, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3652 (pattern : Twelve) (guard : d1867 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1805 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1661, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3646 pattern childGuard
    simpa only [d1661, d1805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1661, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3651 pattern childGuard
    simpa only [d1661, d1805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3653 (pattern : Twelve) (guard : d1867 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1806 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1662, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3642 pattern childGuard
    simpa only [d1662, d1806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1662, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1662, d1806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3654 (pattern : Twelve) (guard : d1867 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1809 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1663, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3652 pattern childGuard
    simpa only [d1663, d1809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1663, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3653 pattern childGuard
    simpa only [d1663, d1809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3655 (pattern : Twelve) (guard : d1867 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1811 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1664, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3643 pattern childGuard
    simpa only [d1664, d1811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1664, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3654 pattern childGuard
    simpa only [d1664, d1811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3656 (pattern : Twelve) (guard : d1867 pattern = 1) : d1668 pattern ≤ (0 : Int) + d1794 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1668, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3274 pattern childGuard
    simpa only [d1668, d1794, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1668, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3638 pattern childGuard
    simpa only [d1668, d1794, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3657 (pattern : Twelve) (guard : d1867 pattern = 1) : d1671 pattern ≤ (0 : Int) + d1801 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1671, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3656 pattern childGuard
    simpa only [d1671, d1801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1671, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3636 pattern childGuard
    simpa only [d1671, d1801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3658 (pattern : Twelve) (guard : d1867 pattern = 1) : d1674 pattern ≤ (0 : Int) + d1807 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1674, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3657 pattern childGuard
    simpa only [d1674, d1807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1674, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3642 pattern childGuard
    simpa only [d1674, d1807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3659 (pattern : Twelve) (guard : d1867 pattern = 1) : d1665 pattern ≤ (0 : Int) + d1783 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1665, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3604 pattern childGuard
    simpa only [d1665, d1783, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1665, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1665, d1783, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3660 (pattern : Twelve) (guard : d1867 pattern = 1) : d1666 pattern ≤ (0 : Int) + d1786 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1666, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3638 pattern childGuard
    simpa only [d1666, d1786, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1666, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3659 pattern childGuard
    simpa only [d1666, d1786, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3661 (pattern : Twelve) (guard : d1867 pattern = 1) : d1669 pattern ≤ (0 : Int) + d1795 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1669, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3475 pattern childGuard
    simpa only [d1669, d1795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1669, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3660 pattern childGuard
    simpa only [d1669, d1795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3662 (pattern : Twelve) (guard : d1867 pattern = 1) : d1672 pattern ≤ (0 : Int) + d1802 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1672, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3661 pattern childGuard
    simpa only [d1672, d1802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1672, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3593 pattern childGuard
    simpa only [d1672, d1802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3663 (pattern : Twelve) (guard : d1867 pattern = 1) : d183 pattern ≤ (0 : Int) + d183 pattern := by
  omega
theorem c3664 (pattern : Twelve) (guard : d1867 pattern = 1) : d1667 pattern ≤ (0 : Int) + d1787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1667, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3459 pattern childGuard
    simpa only [d1667, d1787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1667, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3663 pattern childGuard
    simpa only [d1667, d1787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3665 (pattern : Twelve) (guard : d1867 pattern = 1) : d1670 pattern ≤ (0 : Int) + d1796 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1670, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3592 pattern childGuard
    simpa only [d1670, d1796, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1670, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3664 pattern childGuard
    simpa only [d1670, d1796, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3666 (pattern : Twelve) (guard : d1867 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1626 pattern := by
  omega
theorem c3667 (pattern : Twelve) (guard : d1867 pattern = 1) : d1673 pattern ≤ (0 : Int) + d1803 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1673, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3665 pattern childGuard
    simpa only [d1673, d1803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1673, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3666 pattern childGuard
    simpa only [d1673, d1803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3668 (pattern : Twelve) (guard : d1867 pattern = 1) : d1675 pattern ≤ (0 : Int) + d1808 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1675, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3662 pattern childGuard
    simpa only [d1675, d1808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1675, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3667 pattern childGuard
    simpa only [d1675, d1808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3669 (pattern : Twelve) (guard : d1867 pattern = 1) : d1676 pattern ≤ (0 : Int) + d1810 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1676, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3668 pattern childGuard
    simpa only [d1676, d1810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1676, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3653 pattern childGuard
    simpa only [d1676, d1810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3670 (pattern : Twelve) (guard : d1867 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1677, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3658 pattern childGuard
    simpa only [d1677, d1812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1677, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3669 pattern childGuard
    simpa only [d1677, d1812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3671 (pattern : Twelve) (guard : d1867 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1813 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1678, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3655 pattern childGuard
    simpa only [d1678, d1813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1678, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3670 pattern childGuard
    simpa only [d1678, d1813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3672 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3246 pattern childGuard
    simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3673 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d634 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3246 pattern childGuard
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3674 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d647 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3673 pattern childGuard
    simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3675 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d680 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3672 pattern childGuard
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3674 pattern childGuard
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3676 (pattern : Twelve) (guard : d1866 pattern = 1) : d1 pattern ≤ (0 : Int) + d161 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3253 pattern childGuard
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3677 (pattern : Twelve) (guard : d1866 pattern = 1) : d26 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3676 pattern childGuard
    simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3678 (pattern : Twelve) (guard : d1866 pattern = 1) : d17 pattern ≤ (0 : Int) + d162 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3468 pattern childGuard
    simpa only [d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3679 (pattern : Twelve) (guard : d1866 pattern = 1) : d27 pattern ≤ (0 : Int) + d648 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d27, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3678 pattern childGuard
    simpa only [d27, d648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d27, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d27, d648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3680 (pattern : Twelve) (guard : d1866 pattern = 1) : d50 pattern ≤ (0 : Int) + d681 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d50, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3677 pattern childGuard
    simpa only [d50, d681, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d50, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3679 pattern childGuard
    simpa only [d50, d681, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3681 (pattern : Twelve) (guard : d1866 pattern = 1) : d72 pattern ≤ (0 : Int) + d709 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d72, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3675 pattern childGuard
    simpa only [d72, d709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d72, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3680 pattern childGuard
    simpa only [d72, d709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3682 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d162 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3683 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d649 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3682 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3684 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d682 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3674 pattern childGuard
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3683 pattern childGuard
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3685 (pattern : Twelve) (guard : d1866 pattern = 1) : d18 pattern ≤ (0 : Int) + d635 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d18, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3268 pattern childGuard
    simpa only [d18, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d18, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3500 pattern childGuard
    simpa only [d18, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3686 (pattern : Twelve) (guard : d1866 pattern = 1) : d28 pattern ≤ (0 : Int) + d650 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d28, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3678 pattern childGuard
    simpa only [d28, d650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d28, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3685 pattern childGuard
    simpa only [d28, d650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3687 (pattern : Twelve) (guard : d1866 pattern = 1) : d19 pattern ≤ (0 : Int) + d636 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d19, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3272 pattern childGuard
    simpa only [d19, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d19, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3602 pattern childGuard
    simpa only [d19, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3688 (pattern : Twelve) (guard : d1866 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c3689 (pattern : Twelve) (guard : d1866 pattern = 1) : d29 pattern ≤ (0 : Int) + d651 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d29, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3687 pattern childGuard
    simpa only [d29, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d29, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d29, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3690 (pattern : Twelve) (guard : d1866 pattern = 1) : d51 pattern ≤ (0 : Int) + d683 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d51, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3686 pattern childGuard
    simpa only [d51, d683, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d51, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3689 pattern childGuard
    simpa only [d51, d683, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3691 (pattern : Twelve) (guard : d1866 pattern = 1) : d73 pattern ≤ (0 : Int) + d710 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d73, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3684 pattern childGuard
    simpa only [d73, d710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d73, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3690 pattern childGuard
    simpa only [d73, d710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3692 (pattern : Twelve) (guard : d1866 pattern = 1) : d91 pattern ≤ (0 : Int) + d736 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d91, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3681 pattern childGuard
    simpa only [d91, d736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d91, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3691 pattern childGuard
    simpa only [d91, d736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3693 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d637 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3284 pattern childGuard
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3694 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d652 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3280 pattern childGuard
    simpa only [d30, d652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3693 pattern childGuard
    simpa only [d30, d652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3695 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d638 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3280 pattern childGuard
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3696 (pattern : Twelve) (guard : d1866 pattern = 1) : d13 pattern ≤ (0 : Int) + d13 pattern := by
  omega
theorem c3697 (pattern : Twelve) (guard : d1866 pattern = 1) : d20 pattern ≤ (0 : Int) + d639 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d20, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3289 pattern childGuard
    simpa only [d20, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d20, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3696 pattern childGuard
    simpa only [d20, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3698 (pattern : Twelve) (guard : d1866 pattern = 1) : d31 pattern ≤ (0 : Int) + d653 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d31, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3695 pattern childGuard
    simpa only [d31, d653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d31, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3697 pattern childGuard
    simpa only [d31, d653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3699 (pattern : Twelve) (guard : d1866 pattern = 1) : d52 pattern ≤ (0 : Int) + d684 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d52, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3694 pattern childGuard
    simpa only [d52, d684, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d52, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3698 pattern childGuard
    simpa only [d52, d684, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3700 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d654 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3695 pattern childGuard
    simpa only [d30, d654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d30, d654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3701 (pattern : Twelve) (guard : d1866 pattern = 1) : d17 pattern ≤ (0 : Int) + d158 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3468 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3702 (pattern : Twelve) (guard : d1866 pattern = 1) : d21 pattern ≤ (0 : Int) + d21 pattern := by
  omega
theorem c3703 (pattern : Twelve) (guard : d1866 pattern = 1) : d32 pattern ≤ (0 : Int) + d655 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d32, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d32, d655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d32, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3702 pattern childGuard
    simpa only [d32, d655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3704 (pattern : Twelve) (guard : d1866 pattern = 1) : d53 pattern ≤ (0 : Int) + d685 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d53, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3700 pattern childGuard
    simpa only [d53, d685, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d53, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3703 pattern childGuard
    simpa only [d53, d685, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3705 (pattern : Twelve) (guard : d1866 pattern = 1) : d74 pattern ≤ (0 : Int) + d711 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d74, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3699 pattern childGuard
    simpa only [d74, d711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d74, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3704 pattern childGuard
    simpa only [d74, d711, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3706 (pattern : Twelve) (guard : d1866 pattern = 1) : d22 pattern ≤ (0 : Int) + d22 pattern := by
  omega
theorem c3707 (pattern : Twelve) (guard : d1866 pattern = 1) : d33 pattern ≤ (0 : Int) + d656 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d33, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d33, d656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d33, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d33, d656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3708 (pattern : Twelve) (guard : d1866 pattern = 1) : d54 pattern ≤ (0 : Int) + d686 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d54, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3700 pattern childGuard
    simpa only [d54, d686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d54, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3707 pattern childGuard
    simpa only [d54, d686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3709 (pattern : Twelve) (guard : d1866 pattern = 1) : d23 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3500 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3710 (pattern : Twelve) (guard : d1866 pattern = 1) : d34 pattern ≤ (0 : Int) + d657 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d34, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d34, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d34, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3709 pattern childGuard
    simpa only [d34, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3711 (pattern : Twelve) (guard : d1866 pattern = 1) : d55 pattern ≤ (0 : Int) + d687 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d55, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3710 pattern childGuard
    simpa only [d55, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d55, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3689 pattern childGuard
    simpa only [d55, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3712 (pattern : Twelve) (guard : d1866 pattern = 1) : d75 pattern ≤ (0 : Int) + d712 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d75, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3708 pattern childGuard
    simpa only [d75, d712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d75, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3711 pattern childGuard
    simpa only [d75, d712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3713 (pattern : Twelve) (guard : d1866 pattern = 1) : d92 pattern ≤ (0 : Int) + d737 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d92, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3705 pattern childGuard
    simpa only [d92, d737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d92, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3712 pattern childGuard
    simpa only [d92, d737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3714 (pattern : Twelve) (guard : d1866 pattern = 1) : d102 pattern ≤ (0 : Int) + d754 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d102, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3692 pattern childGuard
    simpa only [d102, d754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d102, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3713 pattern childGuard
    simpa only [d102, d754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3715 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d640 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3716 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d658 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3280 pattern childGuard
    simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3715 pattern childGuard
    simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3717 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d659 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3695 pattern childGuard
    simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3718 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d688 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3716 pattern childGuard
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3717 pattern childGuard
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3719 (pattern : Twelve) (guard : d1866 pattern = 1) : d26 pattern ≤ (0 : Int) + d660 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d26, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3695 pattern childGuard
    simpa only [d26, d660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d26, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d26, d660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3720 (pattern : Twelve) (guard : d1866 pattern = 1) : d27 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d27, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d27, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d27, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d27, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3721 (pattern : Twelve) (guard : d1866 pattern = 1) : d50 pattern ≤ (0 : Int) + d689 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d50, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3719 pattern childGuard
    simpa only [d50, d689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d50, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3720 pattern childGuard
    simpa only [d50, d689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3722 (pattern : Twelve) (guard : d1866 pattern = 1) : d72 pattern ≤ (0 : Int) + d713 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d72, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3718 pattern childGuard
    simpa only [d72, d713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d72, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3721 pattern childGuard
    simpa only [d72, d713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3723 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3717 pattern childGuard
    simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3724 (pattern : Twelve) (guard : d1866 pattern = 1) : d76 pattern ≤ (0 : Int) + d714 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3723 pattern childGuard
    simpa only [d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3711 pattern childGuard
    simpa only [d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3725 (pattern : Twelve) (guard : d1866 pattern = 1) : d93 pattern ≤ (0 : Int) + d738 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d93, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3722 pattern childGuard
    simpa only [d93, d738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d93, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3724 pattern childGuard
    simpa only [d93, d738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3726 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d641 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3324 pattern childGuard
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3727 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d662 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3726 pattern childGuard
    simpa only [d30, d662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d30, d662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3728 (pattern : Twelve) (guard : d1866 pattern = 1) : d35 pattern ≤ (0 : Int) + d663 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d35, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d35, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d35, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d35, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3729 (pattern : Twelve) (guard : d1866 pattern = 1) : d56 pattern ≤ (0 : Int) + d691 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d56, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3727 pattern childGuard
    simpa only [d56, d691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d56, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3728 pattern childGuard
    simpa only [d56, d691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3730 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d657 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d30, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d30, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3731 (pattern : Twelve) (guard : d1866 pattern = 1) : d36 pattern ≤ (0 : Int) + d663 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d36, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d36, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d36, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d36, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3732 (pattern : Twelve) (guard : d1866 pattern = 1) : d57 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d57, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d57, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d57, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3731 pattern childGuard
    simpa only [d57, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3733 (pattern : Twelve) (guard : d1866 pattern = 1) : d77 pattern ≤ (0 : Int) + d715 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d77, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3729 pattern childGuard
    simpa only [d77, d715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d77, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3732 pattern childGuard
    simpa only [d77, d715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3734 (pattern : Twelve) (guard : d1866 pattern = 1) : d56 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d56, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d56, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d56, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3728 pattern childGuard
    simpa only [d56, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3735 (pattern : Twelve) (guard : d1866 pattern = 1) : d78 pattern ≤ (0 : Int) + d716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d78, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3734 pattern childGuard
    simpa only [d78, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d78, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3711 pattern childGuard
    simpa only [d78, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3736 (pattern : Twelve) (guard : d1866 pattern = 1) : d94 pattern ≤ (0 : Int) + d739 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d94, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3733 pattern childGuard
    simpa only [d94, d739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d94, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3735 pattern childGuard
    simpa only [d94, d739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3737 (pattern : Twelve) (guard : d1866 pattern = 1) : d103 pattern ≤ (0 : Int) + d755 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d103, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3725 pattern childGuard
    simpa only [d103, d755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d103, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3736 pattern childGuard
    simpa only [d103, d755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3738 (pattern : Twelve) (guard : d1866 pattern = 1) : d110 pattern ≤ (0 : Int) + d766 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d110, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3714 pattern childGuard
    simpa only [d110, d766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d110, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3737 pattern childGuard
    simpa only [d110, d766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3739 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d642 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3341 pattern childGuard
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3740 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d664 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d30, d664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3739 pattern childGuard
    simpa only [d30, d664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3741 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3715 pattern childGuard
    simpa only [d30, d665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d30, d665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3742 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d693 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3740 pattern childGuard
    simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3741 pattern childGuard
    simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3743 (pattern : Twelve) (guard : d1866 pattern = 1) : d37 pattern ≤ (0 : Int) + d666 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d37, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d37, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d37, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d37, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3744 (pattern : Twelve) (guard : d1866 pattern = 1) : d58 pattern ≤ (0 : Int) + d694 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d58, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3741 pattern childGuard
    simpa only [d58, d694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d58, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3743 pattern childGuard
    simpa only [d58, d694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3745 (pattern : Twelve) (guard : d1866 pattern = 1) : d79 pattern ≤ (0 : Int) + d717 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d79, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3742 pattern childGuard
    simpa only [d79, d717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d79, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3744 pattern childGuard
    simpa only [d79, d717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3746 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d695 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3741 pattern childGuard
    simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3747 (pattern : Twelve) (guard : d1866 pattern = 1) : d80 pattern ≤ (0 : Int) + d718 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d80, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3746 pattern childGuard
    simpa only [d80, d718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d80, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3711 pattern childGuard
    simpa only [d80, d718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3748 (pattern : Twelve) (guard : d1866 pattern = 1) : d95 pattern ≤ (0 : Int) + d740 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d95, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3745 pattern childGuard
    simpa only [d95, d740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d95, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3747 pattern childGuard
    simpa only [d95, d740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3749 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d643 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3356 pattern childGuard
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3750 (pattern : Twelve) (guard : d1866 pattern = 1) : d38 pattern ≤ (0 : Int) + d667 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d38, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3749 pattern childGuard
    simpa only [d38, d667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d38, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3358 pattern childGuard
    simpa only [d38, d667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3751 (pattern : Twelve) (guard : d1866 pattern = 1) : d39 pattern ≤ (0 : Int) + d668 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d39, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d39, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d39, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d39, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3752 (pattern : Twelve) (guard : d1866 pattern = 1) : d59 pattern ≤ (0 : Int) + d696 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d59, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3750 pattern childGuard
    simpa only [d59, d696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d59, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3751 pattern childGuard
    simpa only [d59, d696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3753 (pattern : Twelve) (guard : d1866 pattern = 1) : d38 pattern ≤ (0 : Int) + d669 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d38, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d38, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d38, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3358 pattern childGuard
    simpa only [d38, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3754 (pattern : Twelve) (guard : d1866 pattern = 1) : d40 pattern ≤ (0 : Int) + d668 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d40, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3709 pattern childGuard
    simpa only [d40, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d40, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d40, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3755 (pattern : Twelve) (guard : d1866 pattern = 1) : d60 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d60, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3753 pattern childGuard
    simpa only [d60, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d60, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3754 pattern childGuard
    simpa only [d60, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3756 (pattern : Twelve) (guard : d1866 pattern = 1) : d81 pattern ≤ (0 : Int) + d719 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d81, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3752 pattern childGuard
    simpa only [d81, d719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d81, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3755 pattern childGuard
    simpa only [d81, d719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3757 (pattern : Twelve) (guard : d1866 pattern = 1) : d59 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d59, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3753 pattern childGuard
    simpa only [d59, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d59, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3751 pattern childGuard
    simpa only [d59, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3758 (pattern : Twelve) (guard : d1866 pattern = 1) : d24 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3358 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3587 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3759 (pattern : Twelve) (guard : d1866 pattern = 1) : d41 pattern ≤ (0 : Int) + d669 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d41, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3709 pattern childGuard
    simpa only [d41, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d41, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3758 pattern childGuard
    simpa only [d41, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3760 (pattern : Twelve) (guard : d1866 pattern = 1) : d25 pattern ≤ (0 : Int) + d644 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d25, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3372 pattern childGuard
    simpa only [d25, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d25, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3289 pattern childGuard
    simpa only [d25, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3761 (pattern : Twelve) (guard : d1866 pattern = 1) : d42 pattern ≤ (0 : Int) + d670 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d42, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3760 pattern childGuard
    simpa only [d42, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d42, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d42, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3762 (pattern : Twelve) (guard : d1866 pattern = 1) : d61 pattern ≤ (0 : Int) + d698 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d61, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3759 pattern childGuard
    simpa only [d61, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d61, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3761 pattern childGuard
    simpa only [d61, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3763 (pattern : Twelve) (guard : d1866 pattern = 1) : d82 pattern ≤ (0 : Int) + d720 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d82, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3757 pattern childGuard
    simpa only [d82, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d82, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3762 pattern childGuard
    simpa only [d82, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3764 (pattern : Twelve) (guard : d1866 pattern = 1) : d96 pattern ≤ (0 : Int) + d741 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d96, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3756 pattern childGuard
    simpa only [d96, d741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d96, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3763 pattern childGuard
    simpa only [d96, d741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3765 (pattern : Twelve) (guard : d1866 pattern = 1) : d104 pattern ≤ (0 : Int) + d756 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d104, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3748 pattern childGuard
    simpa only [d104, d756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d104, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3764 pattern childGuard
    simpa only [d104, d756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3766 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d645 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3381 pattern childGuard
    simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3767 (pattern : Twelve) (guard : d1866 pattern = 1) : d30 pattern ≤ (0 : Int) + d671 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3766 pattern childGuard
    simpa only [d30, d671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d30, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d30, d671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3768 (pattern : Twelve) (guard : d1866 pattern = 1) : d56 pattern ≤ (0 : Int) + d699 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d56, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3767 pattern childGuard
    simpa only [d56, d699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d56, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3728 pattern childGuard
    simpa only [d56, d699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3769 (pattern : Twelve) (guard : d1866 pattern = 1) : d77 pattern ≤ (0 : Int) + d721 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d77, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3768 pattern childGuard
    simpa only [d77, d721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d77, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3732 pattern childGuard
    simpa only [d77, d721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3770 (pattern : Twelve) (guard : d1866 pattern = 1) : d94 pattern ≤ (0 : Int) + d742 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d94, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3769 pattern childGuard
    simpa only [d94, d742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d94, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3735 pattern childGuard
    simpa only [d94, d742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3771 (pattern : Twelve) (guard : d1866 pattern = 1) : d105 pattern ≤ (0 : Int) + d757 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d105, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3770 pattern childGuard
    simpa only [d105, d757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d105, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d105, d757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3772 (pattern : Twelve) (guard : d1866 pattern = 1) : d111 pattern ≤ (0 : Int) + d767 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d111, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3765 pattern childGuard
    simpa only [d111, d767, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d111, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3771 pattern childGuard
    simpa only [d111, d767, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3773 (pattern : Twelve) (guard : d1866 pattern = 1) : d114 pattern ≤ (0 : Int) + d772 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d114, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3738 pattern childGuard
    simpa only [d114, d772, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d114, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3772 pattern childGuard
    simpa only [d114, d772, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3774 (pattern : Twelve) (guard : d1866 pattern = 1) : d26 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d26, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d26, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d26, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d26, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3775 (pattern : Twelve) (guard : d1866 pattern = 1) : d50 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3774 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3720 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3776 (pattern : Twelve) (guard : d1866 pattern = 1) : d72 pattern ≤ (0 : Int) + d722 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d72, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d72, d722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d72, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3775 pattern childGuard
    simpa only [d72, d722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3777 (pattern : Twelve) (guard : d1866 pattern = 1) : d28 pattern ≤ (0 : Int) + d672 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d28, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d28, d672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d28, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3685 pattern childGuard
    simpa only [d28, d672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3778 (pattern : Twelve) (guard : d1866 pattern = 1) : d51 pattern ≤ (0 : Int) + d700 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d51, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3777 pattern childGuard
    simpa only [d51, d700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d51, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3689 pattern childGuard
    simpa only [d51, d700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3779 (pattern : Twelve) (guard : d1866 pattern = 1) : d73 pattern ≤ (0 : Int) + d723 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d73, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d73, d723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d73, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3778 pattern childGuard
    simpa only [d73, d723, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
