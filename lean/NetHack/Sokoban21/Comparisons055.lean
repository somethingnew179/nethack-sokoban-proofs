/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons054
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c7700 (pattern : Twelve) (guard : d1867 pattern = 1) : d1764 pattern ≤ (0 : Int) + d1798 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1764, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7699 pattern childGuard
    simpa only [d1764, d1798, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1764, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7655 pattern childGuard
    simpa only [d1764, d1798, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7701 (pattern : Twelve) (guard : d1867 pattern = 1) : d1770 pattern ≤ (0 : Int) + d1804 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1770, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7695 pattern childGuard
    simpa only [d1770, d1804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1770, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7700 pattern childGuard
    simpa only [d1770, d1804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7702 (pattern : Twelve) (guard : d1867 pattern = 1) : d1756 pattern ≤ (0 : Int) + d1791 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1756, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7555 pattern childGuard
    simpa only [d1756, d1791, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1756, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7696 pattern childGuard
    simpa only [d1756, d1791, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7703 (pattern : Twelve) (guard : d1867 pattern = 1) : d1757 pattern ≤ (0 : Int) + d1792 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1757, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7583 pattern childGuard
    simpa only [d1757, d1792, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1757, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1757, d1792, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7704 (pattern : Twelve) (guard : d1867 pattern = 1) : d1765 pattern ≤ (0 : Int) + d1799 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1765, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7702 pattern childGuard
    simpa only [d1765, d1799, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1765, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7703 pattern childGuard
    simpa only [d1765, d1799, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7705 (pattern : Twelve) (guard : d1867 pattern = 1) : d1747 pattern ≤ (0 : Int) + d1782 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1747, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7412 pattern childGuard
    simpa only [d1747, d1782, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1747, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1747, d1782, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7706 (pattern : Twelve) (guard : d1867 pattern = 1) : d1750 pattern ≤ (0 : Int) + d1785 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1750, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7705 pattern childGuard
    simpa only [d1750, d1785, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1750, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7541 pattern childGuard
    simpa only [d1750, d1785, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7707 (pattern : Twelve) (guard : d1867 pattern = 1) : d1758 pattern ≤ (0 : Int) + d1793 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1758, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7654 pattern childGuard
    simpa only [d1758, d1793, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1758, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7706 pattern childGuard
    simpa only [d1758, d1793, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7708 (pattern : Twelve) (guard : d1867 pattern = 1) : d1759 pattern ≤ (0 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7584 pattern childGuard
    simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7709 (pattern : Twelve) (guard : d1867 pattern = 1) : d1766 pattern ≤ (0 : Int) + d1800 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1766, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7707 pattern childGuard
    simpa only [d1766, d1800, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1766, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7708 pattern childGuard
    simpa only [d1766, d1800, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7710 (pattern : Twelve) (guard : d1867 pattern = 1) : d1771 pattern ≤ (0 : Int) + d1805 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1771, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7704 pattern childGuard
    simpa only [d1771, d1805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1771, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7709 pattern childGuard
    simpa only [d1771, d1805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7711 (pattern : Twelve) (guard : d1867 pattern = 1) : d1772 pattern ≤ (0 : Int) + d1806 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1772, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7700 pattern childGuard
    simpa only [d1772, d1806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1772, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1772, d1806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7712 (pattern : Twelve) (guard : d1867 pattern = 1) : d1775 pattern ≤ (0 : Int) + d1809 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1775, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7710 pattern childGuard
    simpa only [d1775, d1809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1775, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7711 pattern childGuard
    simpa only [d1775, d1809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7713 (pattern : Twelve) (guard : d1867 pattern = 1) : d1777 pattern ≤ (0 : Int) + d1811 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1777, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7701 pattern childGuard
    simpa only [d1777, d1811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1777, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7712 pattern childGuard
    simpa only [d1777, d1811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7714 (pattern : Twelve) (guard : d1867 pattern = 1) : d1760 pattern ≤ (0 : Int) + d1794 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1760, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7400 pattern childGuard
    simpa only [d1760, d1794, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1760, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7696 pattern childGuard
    simpa only [d1760, d1794, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7715 (pattern : Twelve) (guard : d1867 pattern = 1) : d1767 pattern ≤ (0 : Int) + d1801 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1767, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7714 pattern childGuard
    simpa only [d1767, d1801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1767, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7694 pattern childGuard
    simpa only [d1767, d1801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7716 (pattern : Twelve) (guard : d1867 pattern = 1) : d1773 pattern ≤ (0 : Int) + d1807 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1773, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7715 pattern childGuard
    simpa only [d1773, d1807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1773, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7700 pattern childGuard
    simpa only [d1773, d1807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7717 (pattern : Twelve) (guard : d1867 pattern = 1) : d1748 pattern ≤ (0 : Int) + d1783 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1748, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7664 pattern childGuard
    simpa only [d1748, d1783, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1748, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1748, d1783, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7718 (pattern : Twelve) (guard : d1867 pattern = 1) : d1751 pattern ≤ (0 : Int) + d1786 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1751, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7696 pattern childGuard
    simpa only [d1751, d1786, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1751, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7717 pattern childGuard
    simpa only [d1751, d1786, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7719 (pattern : Twelve) (guard : d1867 pattern = 1) : d1761 pattern ≤ (0 : Int) + d1795 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1761, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7555 pattern childGuard
    simpa only [d1761, d1795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1761, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7718 pattern childGuard
    simpa only [d1761, d1795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7720 (pattern : Twelve) (guard : d1867 pattern = 1) : d1768 pattern ≤ (0 : Int) + d1802 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1768, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7719 pattern childGuard
    simpa only [d1768, d1802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1768, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7655 pattern childGuard
    simpa only [d1768, d1802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7721 (pattern : Twelve) (guard : d1867 pattern = 1) : d1752 pattern ≤ (0 : Int) + d1787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1752, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7541 pattern childGuard
    simpa only [d1752, d1787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1752, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3663 pattern childGuard
    simpa only [d1752, d1787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7722 (pattern : Twelve) (guard : d1867 pattern = 1) : d1762 pattern ≤ (0 : Int) + d1796 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1762, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7654 pattern childGuard
    simpa only [d1762, d1796, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1762, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7721 pattern childGuard
    simpa only [d1762, d1796, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7723 (pattern : Twelve) (guard : d1867 pattern = 1) : d191 pattern ≤ (0 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d191, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7584 pattern childGuard
    simpa only [d191, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d191, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d191, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7724 (pattern : Twelve) (guard : d1867 pattern = 1) : d202 pattern ≤ (0 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d202, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7723 pattern childGuard
    simpa only [d202, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d202, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d202, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7725 (pattern : Twelve) (guard : d1867 pattern = 1) : d1769 pattern ≤ (0 : Int) + d1803 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1769, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7722 pattern childGuard
    simpa only [d1769, d1803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1769, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7724 pattern childGuard
    simpa only [d1769, d1803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7726 (pattern : Twelve) (guard : d1867 pattern = 1) : d1774 pattern ≤ (0 : Int) + d1808 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1774, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7720 pattern childGuard
    simpa only [d1774, d1808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1774, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7725 pattern childGuard
    simpa only [d1774, d1808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7727 (pattern : Twelve) (guard : d1867 pattern = 1) : d1776 pattern ≤ (0 : Int) + d1810 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1776, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7726 pattern childGuard
    simpa only [d1776, d1810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1776, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7711 pattern childGuard
    simpa only [d1776, d1810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7728 (pattern : Twelve) (guard : d1867 pattern = 1) : d1778 pattern ≤ (0 : Int) + d1812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1778, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7716 pattern childGuard
    simpa only [d1778, d1812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1778, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7727 pattern childGuard
    simpa only [d1778, d1812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7729 (pattern : Twelve) (guard : d1867 pattern = 1) : d1779 pattern ≤ (0 : Int) + d1813 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1779, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7713 pattern childGuard
    simpa only [d1779, d1813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1779, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7728 pattern childGuard
    simpa only [d1779, d1813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7730 (pattern : Twelve) (guard : d1866 pattern = 1) : d7 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4957 pattern childGuard
    simpa only [d1866, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7731 (pattern : Twelve) (guard : d1866 pattern = 1) : d646 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7732 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7733 (pattern : Twelve) (guard : d1866 pattern = 1) : d634 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7734 (pattern : Twelve) (guard : d1866 pattern = 1) : d647 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7733 pattern childGuard
    simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7735 (pattern : Twelve) (guard : d1866 pattern = 1) : d680 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7731 pattern childGuard
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7734 pattern childGuard
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7736 (pattern : Twelve) (guard : d1866 pattern = 1) : d157 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7737 (pattern : Twelve) (guard : d1866 pattern = 1) : d161 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3253 pattern childGuard
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7738 (pattern : Twelve) (guard : d1866 pattern = 1) : d171 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7737 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7739 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d158, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1866, d158, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7740 (pattern : Twelve) (guard : d1866 pattern = 1) : d162 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7739 pattern childGuard
    simpa only [d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7741 (pattern : Twelve) (guard : d1866 pattern = 1) : d648 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d648, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7740 pattern childGuard
    simpa only [d648, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d648, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d648, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7742 (pattern : Twelve) (guard : d1866 pattern = 1) : d681 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d681, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7738 pattern childGuard
    simpa only [d681, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d681, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7741 pattern childGuard
    simpa only [d681, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7743 (pattern : Twelve) (guard : d1866 pattern = 1) : d709 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d709, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7735 pattern childGuard
    simpa only [d709, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d709, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7742 pattern childGuard
    simpa only [d709, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7744 (pattern : Twelve) (guard : d1866 pattern = 1) : d162 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7745 (pattern : Twelve) (guard : d1866 pattern = 1) : d649 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7744 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7746 (pattern : Twelve) (guard : d1866 pattern = 1) : d682 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7734 pattern childGuard
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7745 pattern childGuard
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7747 (pattern : Twelve) (guard : d1866 pattern = 1) : d157 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d157, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1866, d157, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d157, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1866, d157, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7748 (pattern : Twelve) (guard : d1866 pattern = 1) : d160 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d160, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d160, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d160, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1866, d160, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7749 (pattern : Twelve) (guard : d1866 pattern = 1) : d635 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d635, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7747 pattern childGuard
    simpa only [d635, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d635, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7748 pattern childGuard
    simpa only [d635, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7750 (pattern : Twelve) (guard : d1866 pattern = 1) : d650 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d650, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7740 pattern childGuard
    simpa only [d650, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d650, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7749 pattern childGuard
    simpa only [d650, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7751 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d158, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1866, d158, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7752 (pattern : Twelve) (guard : d1866 pattern = 1) : d157 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d157, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1866, d157, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d157, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1866, d157, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7753 (pattern : Twelve) (guard : d1866 pattern = 1) : d636 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d636, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7751 pattern childGuard
    simpa only [d636, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d636, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7752 pattern childGuard
    simpa only [d636, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7754 (pattern : Twelve) (guard : d1866 pattern = 1) : d651 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d651, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7753 pattern childGuard
    simpa only [d651, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d651, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d651, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7755 (pattern : Twelve) (guard : d1866 pattern = 1) : d683 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d683, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7750 pattern childGuard
    simpa only [d683, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d683, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7754 pattern childGuard
    simpa only [d683, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7756 (pattern : Twelve) (guard : d1866 pattern = 1) : d710 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d710, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7746 pattern childGuard
    simpa only [d710, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d710, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7755 pattern childGuard
    simpa only [d710, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7757 (pattern : Twelve) (guard : d1866 pattern = 1) : d736 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d736, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7743 pattern childGuard
    simpa only [d736, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d736, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7756 pattern childGuard
    simpa only [d736, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7758 (pattern : Twelve) (guard : d1866 pattern = 1) : d10 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1609 pattern childGuard
    simpa only [d1866, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7759 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7760 (pattern : Twelve) (guard : d1866 pattern = 1) : d9 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7759 pattern childGuard
    simpa only [d1866, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7761 (pattern : Twelve) (guard : d1866 pattern = 1) : d160 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7762 (pattern : Twelve) (guard : d1866 pattern = 1) : d637 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7760 pattern childGuard
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7763 (pattern : Twelve) (guard : d1866 pattern = 1) : d652 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d652, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d652, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d652, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7762 pattern childGuard
    simpa only [d652, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7764 (pattern : Twelve) (guard : d1866 pattern = 1) : d638 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7765 (pattern : Twelve) (guard : d1866 pattern = 1) : d159 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d159, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1866, d159, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d159, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1866, d159, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7766 (pattern : Twelve) (guard : d1866 pattern = 1) : d639 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d639, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7765 pattern childGuard
    simpa only [d639, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d639, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3696 pattern childGuard
    simpa only [d639, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7767 (pattern : Twelve) (guard : d1866 pattern = 1) : d653 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d653, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7764 pattern childGuard
    simpa only [d653, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d653, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7766 pattern childGuard
    simpa only [d653, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7768 (pattern : Twelve) (guard : d1866 pattern = 1) : d684 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d684, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7763 pattern childGuard
    simpa only [d684, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d684, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7767 pattern childGuard
    simpa only [d684, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7769 (pattern : Twelve) (guard : d1866 pattern = 1) : d654 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d654, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7764 pattern childGuard
    simpa only [d654, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d654, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d654, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7770 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7739 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7771 (pattern : Twelve) (guard : d1866 pattern = 1) : d655 pattern ≤ (0 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d655, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d655, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d655, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3702 pattern childGuard
    simpa only [d655, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7772 (pattern : Twelve) (guard : d1866 pattern = 1) : d685 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d685, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7769 pattern childGuard
    simpa only [d685, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d685, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7771 pattern childGuard
    simpa only [d685, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7773 (pattern : Twelve) (guard : d1866 pattern = 1) : d711 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d711, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7768 pattern childGuard
    simpa only [d711, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d711, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7772 pattern childGuard
    simpa only [d711, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7774 (pattern : Twelve) (guard : d1866 pattern = 1) : d656 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d656, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d656, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d656, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d656, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7775 (pattern : Twelve) (guard : d1866 pattern = 1) : d686 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d686, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7769 pattern childGuard
    simpa only [d686, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d686, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7774 pattern childGuard
    simpa only [d686, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7776 (pattern : Twelve) (guard : d1866 pattern = 1) : d160 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7748 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7777 (pattern : Twelve) (guard : d1866 pattern = 1) : d657 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d657, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d657, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d657, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7776 pattern childGuard
    simpa only [d657, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7778 (pattern : Twelve) (guard : d1866 pattern = 1) : d687 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d687, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7777 pattern childGuard
    simpa only [d687, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d687, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7754 pattern childGuard
    simpa only [d687, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7779 (pattern : Twelve) (guard : d1866 pattern = 1) : d712 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d712, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7775 pattern childGuard
    simpa only [d712, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d712, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7778 pattern childGuard
    simpa only [d712, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7780 (pattern : Twelve) (guard : d1866 pattern = 1) : d737 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d737, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7773 pattern childGuard
    simpa only [d737, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d737, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7779 pattern childGuard
    simpa only [d737, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7781 (pattern : Twelve) (guard : d1866 pattern = 1) : d754 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d754, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7757 pattern childGuard
    simpa only [d754, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d754, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7780 pattern childGuard
    simpa only [d754, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7782 (pattern : Twelve) (guard : d1866 pattern = 1) : d630 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7061 pattern childGuard
    simpa only [d1866, d630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7783 (pattern : Twelve) (guard : d1866 pattern = 1) : d640 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7782 pattern childGuard
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7784 (pattern : Twelve) (guard : d1866 pattern = 1) : d658 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7783 pattern childGuard
    simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7785 (pattern : Twelve) (guard : d1866 pattern = 1) : d659 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7764 pattern childGuard
    simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7786 (pattern : Twelve) (guard : d1866 pattern = 1) : d688 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7784 pattern childGuard
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7785 pattern childGuard
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7787 (pattern : Twelve) (guard : d1866 pattern = 1) : d660 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d660, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7764 pattern childGuard
    simpa only [d660, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d660, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d660, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7788 (pattern : Twelve) (guard : d1866 pattern = 1) : d661 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d661, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d661, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d661, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d661, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7789 (pattern : Twelve) (guard : d1866 pattern = 1) : d689 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d689, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7787 pattern childGuard
    simpa only [d689, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d689, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7788 pattern childGuard
    simpa only [d689, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7790 (pattern : Twelve) (guard : d1866 pattern = 1) : d713 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d713, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7786 pattern childGuard
    simpa only [d713, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d713, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7789 pattern childGuard
    simpa only [d713, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7791 (pattern : Twelve) (guard : d1866 pattern = 1) : d690 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7785 pattern childGuard
    simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7792 (pattern : Twelve) (guard : d1866 pattern = 1) : d714 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7791 pattern childGuard
    simpa only [d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7778 pattern childGuard
    simpa only [d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7793 (pattern : Twelve) (guard : d1866 pattern = 1) : d738 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d738, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7790 pattern childGuard
    simpa only [d738, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d738, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7792 pattern childGuard
    simpa only [d738, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7794 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7795 (pattern : Twelve) (guard : d1866 pattern = 1) : d631 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7794 pattern childGuard
    simpa only [d1866, d631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7796 (pattern : Twelve) (guard : d1866 pattern = 1) : d641 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7795 pattern childGuard
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7797 (pattern : Twelve) (guard : d1866 pattern = 1) : d662 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d662, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7796 pattern childGuard
    simpa only [d662, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d662, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d662, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7798 (pattern : Twelve) (guard : d1866 pattern = 1) : d663 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d663, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d663, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d663, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d663, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7799 (pattern : Twelve) (guard : d1866 pattern = 1) : d691 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d691, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7797 pattern childGuard
    simpa only [d691, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d691, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7798 pattern childGuard
    simpa only [d691, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7800 (pattern : Twelve) (guard : d1866 pattern = 1) : d657 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d657, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d657, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d657, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d657, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7801 (pattern : Twelve) (guard : d1866 pattern = 1) : d663 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d663, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d663, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d663, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d663, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7802 (pattern : Twelve) (guard : d1866 pattern = 1) : d692 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d692, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d692, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d692, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7801 pattern childGuard
    simpa only [d692, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7803 (pattern : Twelve) (guard : d1866 pattern = 1) : d715 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d715, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7799 pattern childGuard
    simpa only [d715, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d715, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7802 pattern childGuard
    simpa only [d715, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7804 (pattern : Twelve) (guard : d1866 pattern = 1) : d692 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d692, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d692, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d692, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7798 pattern childGuard
    simpa only [d692, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7805 (pattern : Twelve) (guard : d1866 pattern = 1) : d716 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d716, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7804 pattern childGuard
    simpa only [d716, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d716, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7778 pattern childGuard
    simpa only [d716, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7806 (pattern : Twelve) (guard : d1866 pattern = 1) : d739 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d739, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7803 pattern childGuard
    simpa only [d739, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d739, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7805 pattern childGuard
    simpa only [d739, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7807 (pattern : Twelve) (guard : d1866 pattern = 1) : d755 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d755, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7793 pattern childGuard
    simpa only [d755, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d755, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7806 pattern childGuard
    simpa only [d755, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7808 (pattern : Twelve) (guard : d1866 pattern = 1) : d766 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d766, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7781 pattern childGuard
    simpa only [d766, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d766, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7807 pattern childGuard
    simpa only [d766, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7809 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7810 (pattern : Twelve) (guard : d1866 pattern = 1) : d16 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7809 pattern childGuard
    simpa only [d1866, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7811 (pattern : Twelve) (guard : d1866 pattern = 1) : d642 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7810 pattern childGuard
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7812 (pattern : Twelve) (guard : d1866 pattern = 1) : d664 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d664, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7782 pattern childGuard
    simpa only [d664, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d664, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7811 pattern childGuard
    simpa only [d664, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7813 (pattern : Twelve) (guard : d1866 pattern = 1) : d665 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d665, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7783 pattern childGuard
    simpa only [d665, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d665, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d665, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7814 (pattern : Twelve) (guard : d1866 pattern = 1) : d693 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7812 pattern childGuard
    simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7813 pattern childGuard
    simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7815 (pattern : Twelve) (guard : d1866 pattern = 1) : d159 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1866, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1866, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7816 (pattern : Twelve) (guard : d1866 pattern = 1) : d666 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d666, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d666, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d666, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d666, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7817 (pattern : Twelve) (guard : d1866 pattern = 1) : d694 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d694, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7813 pattern childGuard
    simpa only [d694, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d694, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7816 pattern childGuard
    simpa only [d694, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7818 (pattern : Twelve) (guard : d1866 pattern = 1) : d717 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d717, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7814 pattern childGuard
    simpa only [d717, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d717, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7817 pattern childGuard
    simpa only [d717, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7819 (pattern : Twelve) (guard : d1866 pattern = 1) : d695 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7813 pattern childGuard
    simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7820 (pattern : Twelve) (guard : d1866 pattern = 1) : d718 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d718, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7819 pattern childGuard
    simpa only [d718, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d718, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7778 pattern childGuard
    simpa only [d718, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7821 (pattern : Twelve) (guard : d1866 pattern = 1) : d740 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d740, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7818 pattern childGuard
    simpa only [d740, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d740, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7820 pattern childGuard
    simpa only [d740, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7822 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7823 (pattern : Twelve) (guard : d1866 pattern = 1) : d632 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7822 pattern childGuard
    simpa only [d1866, d632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7824 (pattern : Twelve) (guard : d1866 pattern = 1) : d643 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7823 pattern childGuard
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7825 (pattern : Twelve) (guard : d1866 pattern = 1) : d13 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1866, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1866, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7826 (pattern : Twelve) (guard : d1866 pattern = 1) : d667 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d667, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7824 pattern childGuard
    simpa only [d667, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d667, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d667, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7827 (pattern : Twelve) (guard : d1866 pattern = 1) : d668 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d668, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d668, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d668, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d668, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7828 (pattern : Twelve) (guard : d1866 pattern = 1) : d696 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d696, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7826 pattern childGuard
    simpa only [d696, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d696, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7827 pattern childGuard
    simpa only [d696, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7829 (pattern : Twelve) (guard : d1866 pattern = 1) : d669 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d669, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d669, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d669, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d669, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7830 (pattern : Twelve) (guard : d1866 pattern = 1) : d668 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d668, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7776 pattern childGuard
    simpa only [d668, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d668, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d668, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7831 (pattern : Twelve) (guard : d1866 pattern = 1) : d697 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d697, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7829 pattern childGuard
    simpa only [d697, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d697, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7830 pattern childGuard
    simpa only [d697, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7832 (pattern : Twelve) (guard : d1866 pattern = 1) : d719 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d719, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7828 pattern childGuard
    simpa only [d719, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d719, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7831 pattern childGuard
    simpa only [d719, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7833 (pattern : Twelve) (guard : d1866 pattern = 1) : d697 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d697, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7829 pattern childGuard
    simpa only [d697, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d697, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7827 pattern childGuard
    simpa only [d697, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7834 (pattern : Twelve) (guard : d1866 pattern = 1) : d13 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d13, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1866, d13, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d13, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1866, d13, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7835 (pattern : Twelve) (guard : d1866 pattern = 1) : d13 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7834 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7836 (pattern : Twelve) (guard : d1866 pattern = 1) : d669 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d669, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7776 pattern childGuard
    simpa only [d669, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d669, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7835 pattern childGuard
    simpa only [d669, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7837 (pattern : Twelve) (guard : d1866 pattern = 1) : d160 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d160, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d160, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d160, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1866, d160, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7838 (pattern : Twelve) (guard : d1866 pattern = 1) : d644 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d644, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7837 pattern childGuard
    simpa only [d644, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d644, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7765 pattern childGuard
    simpa only [d644, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7839 (pattern : Twelve) (guard : d1866 pattern = 1) : d670 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d670, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7838 pattern childGuard
    simpa only [d670, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d670, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d670, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
