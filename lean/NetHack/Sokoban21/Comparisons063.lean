/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons062
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c8820 (pattern : Twelve) (guard : d1867 pattern = 1) : d1606 pattern ≤ (0 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1606, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8802 pattern childGuard
    simpa only [d1606, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1606, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1606, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8821 (pattern : Twelve) (guard : d1867 pattern = 1) : d1609 pattern ≤ (0 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1609, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8819 pattern childGuard
    simpa only [d1609, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1609, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8820 pattern childGuard
    simpa only [d1609, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8822 (pattern : Twelve) (guard : d1867 pattern = 1) : d1612 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1612, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8803 pattern childGuard
    simpa only [d1612, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1612, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8821 pattern childGuard
    simpa only [d1612, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8823 (pattern : Twelve) (guard : d1867 pattern = 1) : d1615 pattern ≤ (0 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1615, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8791 pattern childGuard
    simpa only [d1615, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1615, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8822 pattern childGuard
    simpa only [d1615, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8824 (pattern : Twelve) (guard : d1867 pattern = 1) : d1788 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1788, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8492 pattern childGuard
    simpa only [d1788, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1788, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8793 pattern childGuard
    simpa only [d1788, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8825 (pattern : Twelve) (guard : d1867 pattern = 1) : d1789 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1789, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8573 pattern childGuard
    simpa only [d1789, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1789, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1789, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8826 (pattern : Twelve) (guard : d1867 pattern = 1) : d1797 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1797, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8824 pattern childGuard
    simpa only [d1797, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1797, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8825 pattern childGuard
    simpa only [d1797, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8827 (pattern : Twelve) (guard : d1867 pattern = 1) : d1780 pattern ≤ (0 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1780, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8793 pattern childGuard
    simpa only [d1780, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1780, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8503 pattern childGuard
    simpa only [d1780, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8828 (pattern : Twelve) (guard : d1867 pattern = 1) : d1781 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1781, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8793 pattern childGuard
    simpa only [d1781, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1781, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1781, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8829 (pattern : Twelve) (guard : d1867 pattern = 1) : d1784 pattern ≤ (0 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1784, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8827 pattern childGuard
    simpa only [d1784, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1784, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8828 pattern childGuard
    simpa only [d1784, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8830 (pattern : Twelve) (guard : d1867 pattern = 1) : d1790 pattern ≤ (0 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1790, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8765 pattern childGuard
    simpa only [d1790, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1790, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8829 pattern childGuard
    simpa only [d1790, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8831 (pattern : Twelve) (guard : d1867 pattern = 1) : d1798 pattern ≤ (0 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1798, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8830 pattern childGuard
    simpa only [d1798, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1798, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8783 pattern childGuard
    simpa only [d1798, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8832 (pattern : Twelve) (guard : d1867 pattern = 1) : d1804 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1804, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8826 pattern childGuard
    simpa only [d1804, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1804, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8831 pattern childGuard
    simpa only [d1804, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8833 (pattern : Twelve) (guard : d1867 pattern = 1) : d1791 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1791, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8669 pattern childGuard
    simpa only [d1791, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1791, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8827 pattern childGuard
    simpa only [d1791, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8834 (pattern : Twelve) (guard : d1867 pattern = 1) : d1792 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1792, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8699 pattern childGuard
    simpa only [d1792, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1792, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1792, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8835 (pattern : Twelve) (guard : d1867 pattern = 1) : d1799 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1799, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8833 pattern childGuard
    simpa only [d1799, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1799, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8834 pattern childGuard
    simpa only [d1799, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8836 (pattern : Twelve) (guard : d1867 pattern = 1) : d1782 pattern ≤ (0 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1782, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8503 pattern childGuard
    simpa only [d1782, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1782, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1782, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8837 (pattern : Twelve) (guard : d1867 pattern = 1) : d1785 pattern ≤ (0 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1785, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8836 pattern childGuard
    simpa only [d1785, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1785, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8654 pattern childGuard
    simpa only [d1785, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8838 (pattern : Twelve) (guard : d1867 pattern = 1) : d1793 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1793, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8782 pattern childGuard
    simpa only [d1793, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1793, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8837 pattern childGuard
    simpa only [d1793, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8839 (pattern : Twelve) (guard : d1867 pattern = 1) : d1800 pattern ≤ (0 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1800, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8838 pattern childGuard
    simpa only [d1800, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1800, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3650 pattern childGuard
    simpa only [d1800, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8840 (pattern : Twelve) (guard : d1867 pattern = 1) : d1805 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1805, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8835 pattern childGuard
    simpa only [d1805, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1805, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8839 pattern childGuard
    simpa only [d1805, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8841 (pattern : Twelve) (guard : d1867 pattern = 1) : d1806 pattern ≤ (0 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1806, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8831 pattern childGuard
    simpa only [d1806, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1806, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1806, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8842 (pattern : Twelve) (guard : d1867 pattern = 1) : d1809 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1809, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8840 pattern childGuard
    simpa only [d1809, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1809, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8841 pattern childGuard
    simpa only [d1809, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8843 (pattern : Twelve) (guard : d1867 pattern = 1) : d1811 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1811, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8832 pattern childGuard
    simpa only [d1811, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1811, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8842 pattern childGuard
    simpa only [d1811, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8844 (pattern : Twelve) (guard : d1867 pattern = 1) : d1794 pattern ≤ (0 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1794, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8492 pattern childGuard
    simpa only [d1794, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1794, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8827 pattern childGuard
    simpa only [d1794, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8845 (pattern : Twelve) (guard : d1867 pattern = 1) : d1801 pattern ≤ (0 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1801, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8844 pattern childGuard
    simpa only [d1801, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1801, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8825 pattern childGuard
    simpa only [d1801, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8846 (pattern : Twelve) (guard : d1867 pattern = 1) : d1807 pattern ≤ (0 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1807, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8845 pattern childGuard
    simpa only [d1807, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1807, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8831 pattern childGuard
    simpa only [d1807, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8847 (pattern : Twelve) (guard : d1867 pattern = 1) : d1783 pattern ≤ (0 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1783, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8793 pattern childGuard
    simpa only [d1783, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1783, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1783, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8848 (pattern : Twelve) (guard : d1867 pattern = 1) : d1786 pattern ≤ (0 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1786, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8827 pattern childGuard
    simpa only [d1786, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1786, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8847 pattern childGuard
    simpa only [d1786, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8849 (pattern : Twelve) (guard : d1867 pattern = 1) : d1795 pattern ≤ (0 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1795, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8669 pattern childGuard
    simpa only [d1795, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1795, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8848 pattern childGuard
    simpa only [d1795, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8850 (pattern : Twelve) (guard : d1867 pattern = 1) : d1802 pattern ≤ (0 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1802, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8849 pattern childGuard
    simpa only [d1802, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1802, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8783 pattern childGuard
    simpa only [d1802, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8851 (pattern : Twelve) (guard : d1867 pattern = 1) : d1787 pattern ≤ (0 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1787, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8654 pattern childGuard
    simpa only [d1787, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1787, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3663 pattern childGuard
    simpa only [d1787, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8852 (pattern : Twelve) (guard : d1867 pattern = 1) : d1796 pattern ≤ (0 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1796, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8782 pattern childGuard
    simpa only [d1796, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1796, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8851 pattern childGuard
    simpa only [d1796, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8853 (pattern : Twelve) (guard : d1867 pattern = 1) : d1803 pattern ≤ (0 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1803, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8852 pattern childGuard
    simpa only [d1803, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1803, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3666 pattern childGuard
    simpa only [d1803, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8854 (pattern : Twelve) (guard : d1867 pattern = 1) : d1808 pattern ≤ (0 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1808, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8850 pattern childGuard
    simpa only [d1808, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1808, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8853 pattern childGuard
    simpa only [d1808, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8855 (pattern : Twelve) (guard : d1867 pattern = 1) : d1810 pattern ≤ (0 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1810, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8854 pattern childGuard
    simpa only [d1810, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1810, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8841 pattern childGuard
    simpa only [d1810, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8856 (pattern : Twelve) (guard : d1867 pattern = 1) : d1812 pattern ≤ (0 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1812, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8846 pattern childGuard
    simpa only [d1812, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1812, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8855 pattern childGuard
    simpa only [d1812, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8857 (pattern : Twelve) (guard : d1867 pattern = 1) : d1813 pattern ≤ (0 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1813, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8843 pattern childGuard
    simpa only [d1813, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1813, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8856 pattern childGuard
    simpa only [d1813, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8858 (pattern : Twelve) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d116 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8859 (pattern : Twelve) (guard : d0 pattern = 1) : d871 pattern ≤ (0 : Int) + d871 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8860 (pattern : Twelve) (guard : d0 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1323 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8861 (pattern : Twelve) (guard : d0 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1664 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8862 (pattern : Twelve) (guard : d0 pattern = 1) : d111 pattern ≤ (0 : Int) + d359 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8863 (pattern : Twelve) (guard : d1868 pattern = 1) : d114 pattern ≤ (0 : Int) + d361 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d114, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4080 pattern childGuard
    simpa only [d1868, d114, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d114, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8862 pattern childGuard
    simpa only [d1868, d114, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8864 (pattern : Twelve) (guard : d0 pattern = 1) : d113 pattern ≤ (0 : Int) + d356 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8865 (pattern : Twelve) (guard : d1868 pattern = 1) : d115 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4085 pattern childGuard
    simpa only [d1868, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8864 pattern childGuard
    simpa only [d1868, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8866 (pattern : Twelve) (guard : d1868 pattern = 1) : d116 pattern ≤ (0 : Int) + d362 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d116, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8863 pattern childGuard
    simpa only [d116, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d116, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8865 pattern childGuard
    simpa only [d116, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8867 (pattern : Twelve) (guard : d0 pattern = 1) : d111 pattern ≤ (0 : Int) + d360 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8868 (pattern : Twelve) (guard : d1868 pattern = 1) : d114 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4090 pattern childGuard
    simpa only [d1868, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8867 pattern childGuard
    simpa only [d1868, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8869 (pattern : Twelve) (guard : d1868 pattern = 1) : d116 pattern ≤ (0 : Int) + d363 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d116, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8868 pattern childGuard
    simpa only [d116, d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d116, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8865 pattern childGuard
    simpa only [d116, d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8870 (pattern : Twelve) (guard : d1868 pattern = 1) : d116 pattern ≤ (0 : Int) + d364 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8866 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8869 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8871 (pattern : Twelve) (guard : d1868 pattern = 1) : d116 pattern ≤ (0 : Int) + d365 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8870 pattern childGuard
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8869 pattern childGuard
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8872 (pattern : Twelve) (guard : d0 pattern = 1) : d867 pattern ≤ (0 : Int) + d1024 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8873 (pattern : Twelve) (guard : d1868 pattern = 1) : d869 pattern ≤ (0 : Int) + d1025 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d869, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4098 pattern childGuard
    simpa only [d1868, d869, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d869, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8872 pattern childGuard
    simpa only [d1868, d869, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8874 (pattern : Twelve) (guard : d0 pattern = 1) : d868 pattern ≤ (0 : Int) + d1022 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8875 (pattern : Twelve) (guard : d1868 pattern = 1) : d870 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c765 pattern childGuard
    simpa only [d1868, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8874 pattern childGuard
    simpa only [d1868, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8876 (pattern : Twelve) (guard : d1868 pattern = 1) : d871 pattern ≤ (0 : Int) + d1026 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d871, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8873 pattern childGuard
    simpa only [d871, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d871, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8875 pattern childGuard
    simpa only [d871, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8877 (pattern : Twelve) (guard : d0 pattern = 1) : d867 pattern ≤ (0 : Int) + d1021 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8878 (pattern : Twelve) (guard : d1868 pattern = 1) : d869 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c772 pattern childGuard
    simpa only [d1868, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8877 pattern childGuard
    simpa only [d1868, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8879 (pattern : Twelve) (guard : d1868 pattern = 1) : d871 pattern ≤ (0 : Int) + d1027 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d871, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8878 pattern childGuard
    simpa only [d871, d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d871, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8875 pattern childGuard
    simpa only [d871, d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8880 (pattern : Twelve) (guard : d1868 pattern = 1) : d871 pattern ≤ (0 : Int) + d1028 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8876 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8879 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8881 (pattern : Twelve) (guard : d1868 pattern = 1) : d871 pattern ≤ (0 : Int) + d1029 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8880 pattern childGuard
    simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8879 pattern childGuard
    simpa only [d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8882 (pattern : Twelve) (guard : d0 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8883 (pattern : Twelve) (guard : d1868 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1439 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1321, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4107 pattern childGuard
    simpa only [d1868, d1321, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1321, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8882 pattern childGuard
    simpa only [d1868, d1321, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8884 (pattern : Twelve) (guard : d0 pattern = 1) : d1320 pattern ≤ (0 : Int) + d1437 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8885 (pattern : Twelve) (guard : d1868 pattern = 1) : d1322 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d1868, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8884 pattern childGuard
    simpa only [d1868, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8886 (pattern : Twelve) (guard : d1868 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1440 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1323, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8883 pattern childGuard
    simpa only [d1323, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1323, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8885 pattern childGuard
    simpa only [d1323, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8887 (pattern : Twelve) (guard : d1868 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c796 pattern childGuard
    simpa only [d1868, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8882 pattern childGuard
    simpa only [d1868, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8888 (pattern : Twelve) (guard : d1868 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1323, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8887 pattern childGuard
    simpa only [d1323, d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1323, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8885 pattern childGuard
    simpa only [d1323, d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8889 (pattern : Twelve) (guard : d1868 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1442 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8886 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8888 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8890 (pattern : Twelve) (guard : d1868 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1443 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8889 pattern childGuard
    simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8888 pattern childGuard
    simpa only [d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8891 (pattern : Twelve) (guard : d0 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1715 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8892 (pattern : Twelve) (guard : d1868 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c805 pattern childGuard
    simpa only [d1868, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8891 pattern childGuard
    simpa only [d1868, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8893 (pattern : Twelve) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d156 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8894 (pattern : Twelve) (guard : d0 pattern = 1) : d871 pattern ≤ (0 : Int) + d907 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8895 (pattern : Twelve) (guard : d0 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1354 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8896 (pattern : Twelve) (guard : d0 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1678 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8897 (pattern : Twelve) (guard : d1848 pattern = 1) : d32 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1431 pattern childGuard
    simpa only [d1848, d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8898 (pattern : Twelve) (guard : d1848 pattern = 1) : d53 pattern ≤ (0 : Int) + d376 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d53, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1285 pattern childGuard
    simpa only [d53, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d53, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8897 pattern childGuard
    simpa only [d53, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8899 (pattern : Twelve) (guard : d1848 pattern = 1) : d74 pattern ≤ (0 : Int) + d391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d74, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2554 pattern childGuard
    simpa only [d74, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d74, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8898 pattern childGuard
    simpa only [d74, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8900 (pattern : Twelve) (guard : d1848 pattern = 1) : d75 pattern ≤ (0 : Int) + d392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d75, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6539 pattern childGuard
    simpa only [d75, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d75, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4158 pattern childGuard
    simpa only [d75, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8901 (pattern : Twelve) (guard : d1848 pattern = 1) : d92 pattern ≤ (0 : Int) + d403 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d92, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8899 pattern childGuard
    simpa only [d92, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d92, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8900 pattern childGuard
    simpa only [d92, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8902 (pattern : Twelve) (guard : d1848 pattern = 1) : d102 pattern ≤ (0 : Int) + d409 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4153 pattern childGuard
    simpa only [d102, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8901 pattern childGuard
    simpa only [d102, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8903 (pattern : Twelve) (guard : d1848 pattern = 1) : d57 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d57, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d57, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d57, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2752 pattern childGuard
    simpa only [d57, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8904 (pattern : Twelve) (guard : d1848 pattern = 1) : d77 pattern ≤ (0 : Int) + d393 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2567 pattern childGuard
    simpa only [d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8903 pattern childGuard
    simpa only [d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8905 (pattern : Twelve) (guard : d1848 pattern = 1) : d78 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d78, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4158 pattern childGuard
    simpa only [d78, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8906 (pattern : Twelve) (guard : d1848 pattern = 1) : d94 pattern ≤ (0 : Int) + d404 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8904 pattern childGuard
    simpa only [d94, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8905 pattern childGuard
    simpa only [d94, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8907 (pattern : Twelve) (guard : d1848 pattern = 1) : d103 pattern ≤ (0 : Int) + d410 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4160 pattern childGuard
    simpa only [d103, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8906 pattern childGuard
    simpa only [d103, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8908 (pattern : Twelve) (guard : d1848 pattern = 1) : d110 pattern ≤ (0 : Int) + d415 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8902 pattern childGuard
    simpa only [d110, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8907 pattern childGuard
    simpa only [d110, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8909 (pattern : Twelve) (guard : d1848 pattern = 1) : d37 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d37, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d37, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d37, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d1848, d37, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8910 (pattern : Twelve) (guard : d1848 pattern = 1) : d58 pattern ≤ (0 : Int) + d382 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d58, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1325 pattern childGuard
    simpa only [d58, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d58, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8909 pattern childGuard
    simpa only [d58, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8911 (pattern : Twelve) (guard : d1848 pattern = 1) : d79 pattern ≤ (0 : Int) + d395 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d79, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2575 pattern childGuard
    simpa only [d79, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d79, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8910 pattern childGuard
    simpa only [d79, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8912 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d396 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2686 pattern childGuard
    simpa only [d80, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4158 pattern childGuard
    simpa only [d80, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8913 (pattern : Twelve) (guard : d1848 pattern = 1) : d95 pattern ≤ (0 : Int) + d405 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8911 pattern childGuard
    simpa only [d95, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8912 pattern childGuard
    simpa only [d95, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8914 (pattern : Twelve) (guard : d1848 pattern = 1) : d60 pattern ≤ (0 : Int) + d384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d60, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d60, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d60, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2768 pattern childGuard
    simpa only [d60, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8915 (pattern : Twelve) (guard : d1848 pattern = 1) : d81 pattern ≤ (0 : Int) + d397 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d81, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d81, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d81, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8914 pattern childGuard
    simpa only [d81, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8916 (pattern : Twelve) (guard : d1848 pattern = 1) : d61 pattern ≤ (0 : Int) + d385 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d61, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d61, d385, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d61, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d61, d385, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8917 (pattern : Twelve) (guard : d1848 pattern = 1) : d82 pattern ≤ (0 : Int) + d398 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d82, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d82, d398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d82, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8916 pattern childGuard
    simpa only [d82, d398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8918 (pattern : Twelve) (guard : d1848 pattern = 1) : d96 pattern ≤ (0 : Int) + d406 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d96, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8915 pattern childGuard
    simpa only [d96, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d96, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8917 pattern childGuard
    simpa only [d96, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8919 (pattern : Twelve) (guard : d1848 pattern = 1) : d104 pattern ≤ (0 : Int) + d411 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d104, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8913 pattern childGuard
    simpa only [d104, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d104, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8918 pattern childGuard
    simpa only [d104, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8920 (pattern : Twelve) (guard : d1848 pattern = 1) : d77 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d77, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8903 pattern childGuard
    simpa only [d77, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8921 (pattern : Twelve) (guard : d1848 pattern = 1) : d94 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8920 pattern childGuard
    simpa only [d94, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8905 pattern childGuard
    simpa only [d94, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8922 (pattern : Twelve) (guard : d1848 pattern = 1) : d105 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d105, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8921 pattern childGuard
    simpa only [d105, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d105, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d105, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8923 (pattern : Twelve) (guard : d1848 pattern = 1) : d111 pattern ≤ (0 : Int) + d416 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d111, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8919 pattern childGuard
    simpa only [d111, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d111, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8922 pattern childGuard
    simpa only [d111, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8924 (pattern : Twelve) (guard : d1848 pattern = 1) : d114 pattern ≤ (0 : Int) + d419 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d114, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8908 pattern childGuard
    simpa only [d114, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d114, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8923 pattern childGuard
    simpa only [d114, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8925 (pattern : Twelve) (guard : d1848 pattern = 1) : d53 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d53, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d53, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d53, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8897 pattern childGuard
    simpa only [d53, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8926 (pattern : Twelve) (guard : d1848 pattern = 1) : d74 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d74, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2602 pattern childGuard
    simpa only [d74, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d74, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8925 pattern childGuard
    simpa only [d74, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8927 (pattern : Twelve) (guard : d1848 pattern = 1) : d75 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d75, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6576 pattern childGuard
    simpa only [d75, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d75, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4158 pattern childGuard
    simpa only [d75, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8928 (pattern : Twelve) (guard : d1848 pattern = 1) : d92 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d92, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8926 pattern childGuard
    simpa only [d92, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d92, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8927 pattern childGuard
    simpa only [d92, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8929 (pattern : Twelve) (guard : d1848 pattern = 1) : d102 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4197 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8928 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8930 (pattern : Twelve) (guard : d1848 pattern = 1) : d103 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4182 pattern childGuard
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8921 pattern childGuard
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8931 (pattern : Twelve) (guard : d1848 pattern = 1) : d110 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8929 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8930 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8932 (pattern : Twelve) (guard : d1848 pattern = 1) : d58 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d58, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d58, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d58, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8909 pattern childGuard
    simpa only [d58, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8933 (pattern : Twelve) (guard : d1848 pattern = 1) : d79 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d79, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d79, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d79, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8932 pattern childGuard
    simpa only [d79, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8934 (pattern : Twelve) (guard : d1848 pattern = 1) : d95 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8933 pattern childGuard
    simpa only [d95, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4186 pattern childGuard
    simpa only [d95, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8935 (pattern : Twelve) (guard : d1848 pattern = 1) : d104 pattern ≤ (0 : Int) + d413 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d104, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8934 pattern childGuard
    simpa only [d104, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d104, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8918 pattern childGuard
    simpa only [d104, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8936 (pattern : Twelve) (guard : d1848 pattern = 1) : d111 pattern ≤ (0 : Int) + d417 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d111, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8935 pattern childGuard
    simpa only [d111, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d111, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8922 pattern childGuard
    simpa only [d111, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8937 (pattern : Twelve) (guard : d1848 pattern = 1) : d114 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d114, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8931 pattern childGuard
    simpa only [d114, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d114, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8936 pattern childGuard
    simpa only [d114, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8938 (pattern : Twelve) (guard : d1848 pattern = 1) : d114 pattern ≤ (0 : Int) + d422 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8924 pattern childGuard
    simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8937 pattern childGuard
    simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8939 (pattern : Twelve) (guard : d1848 pattern = 1) : d114 pattern ≤ (0 : Int) + d423 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8938 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8937 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8940 (pattern : Twelve) (guard : d1848 pattern = 1) : d120 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d120, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d120, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d120, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d1848, d120, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8941 (pattern : Twelve) (guard : d1848 pattern = 1) : d129 pattern ≤ (0 : Int) + d378 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d129, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8940 pattern childGuard
    simpa only [d129, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d129, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d129, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8942 (pattern : Twelve) (guard : d1848 pattern = 1) : d136 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d136, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8941 pattern childGuard
    simpa only [d136, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8943 (pattern : Twelve) (guard : d1848 pattern = 1) : d144 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4180 pattern childGuard
    simpa only [d144, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8942 pattern childGuard
    simpa only [d144, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8944 (pattern : Twelve) (guard : d1848 pattern = 1) : d121 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d121, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d121, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d121, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1290 pattern childGuard
    simpa only [d1848, d121, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8945 (pattern : Twelve) (guard : d1848 pattern = 1) : d130 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d130, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8944 pattern childGuard
    simpa only [d130, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d130, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2752 pattern childGuard
    simpa only [d130, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8946 (pattern : Twelve) (guard : d1848 pattern = 1) : d137 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d137, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2602 pattern childGuard
    simpa only [d137, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d137, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8945 pattern childGuard
    simpa only [d137, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8947 (pattern : Twelve) (guard : d1848 pattern = 1) : d138 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d138, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d138, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d138, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8941 pattern childGuard
    simpa only [d138, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8948 (pattern : Twelve) (guard : d1848 pattern = 1) : d145 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d145, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8946 pattern childGuard
    simpa only [d145, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d145, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8947 pattern childGuard
    simpa only [d145, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8949 (pattern : Twelve) (guard : d1848 pattern = 1) : d149 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8943 pattern childGuard
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8948 pattern childGuard
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8950 (pattern : Twelve) (guard : d1848 pattern = 1) : d139 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d139, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d139, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d139, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8945 pattern childGuard
    simpa only [d139, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8951 (pattern : Twelve) (guard : d1848 pattern = 1) : d146 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d146, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8950 pattern childGuard
    simpa only [d146, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d146, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8947 pattern childGuard
    simpa only [d146, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8952 (pattern : Twelve) (guard : d1848 pattern = 1) : d150 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8943 pattern childGuard
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8951 pattern childGuard
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8953 (pattern : Twelve) (guard : d1848 pattern = 1) : d153 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8949 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8952 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8954 (pattern : Twelve) (guard : d1848 pattern = 1) : d122 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d122, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d122, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d122, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1334 pattern childGuard
    simpa only [d1848, d122, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8955 (pattern : Twelve) (guard : d1848 pattern = 1) : d131 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d131, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8944 pattern childGuard
    simpa only [d131, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d131, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8954 pattern childGuard
    simpa only [d131, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8956 (pattern : Twelve) (guard : d1848 pattern = 1) : d140 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d140, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d140, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d140, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8955 pattern childGuard
    simpa only [d140, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8957 (pattern : Twelve) (guard : d1848 pattern = 1) : d141 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d141, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6600 pattern childGuard
    simpa only [d141, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d141, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8941 pattern childGuard
    simpa only [d141, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8958 (pattern : Twelve) (guard : d1848 pattern = 1) : d147 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d147, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8956 pattern childGuard
    simpa only [d147, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d147, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8957 pattern childGuard
    simpa only [d147, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8959 (pattern : Twelve) (guard : d1848 pattern = 1) : d124 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d124, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d124, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d124, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6663 pattern childGuard
    simpa only [d1848, d124, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
