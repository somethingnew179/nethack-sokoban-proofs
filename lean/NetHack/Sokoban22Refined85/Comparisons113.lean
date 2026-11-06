/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons112
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15820 (p : Pattern) (guard : d4475 p = 1) : d1800 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15819 p hg
    simpa only [d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15802 p hg
    simpa only [d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15821 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15822 (p : Pattern) (guard : d1 p = 1) : d356 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15823 (p : Pattern) (guard : d1 p = 1) : d1802 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15822 p hg
    simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15824 (p : Pattern) (guard : d1 p = 1) : d1803 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15823 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15822 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15825 (p : Pattern) (guard : d4474 p = 1) : d1804 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15824 p hg
    simpa only [d4474, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15826 (p : Pattern) (guard : d4475 p = 1) : d1805 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15821 p hg
    simpa only [d4475, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15825 p hg
    simpa only [d4475, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15827 (p : Pattern) (guard : d4475 p = 1) : d1806 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15826 p hg
    simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15828 (p : Pattern) (guard : d4475 p = 1) : d1807 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15820 p hg
    simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15827 p hg
    simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15829 (p : Pattern) (guard : d4475 p = 1) : d1808 p ≤ (2 : Int) + d4492 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1808, d4492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15804 p hg
    simpa only [d1808, d4492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1808, d4492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15828 p hg
    simpa only [d1808, d4492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15830 (p : Pattern) (guard : d0 p = 1) : d1813 p ≤ (2 : Int) + d4492 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15831 (p : Pattern) (guard : d4476 p = 1) : d1814 p ≤ (2 : Int) + d4492 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15829 p hg
    simpa only [d4476, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15830 p hg
    simpa only [d4476, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15832 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15833 (p : Pattern) (guard : d1 p = 1) : d1710 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15834 (p : Pattern) (guard : d1 p = 1) : d1711 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15833 p hg
    simpa only [d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15835 (p : Pattern) (guard : d1 p = 1) : d1712 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12153 p hg
    simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15834 p hg
    simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15836 (p : Pattern) (guard : d1 p = 1) : d1713 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15837 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15836 p hg
    simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15838 (p : Pattern) (guard : d1 p = 1) : d1715 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12152 p hg
    simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15839 (p : Pattern) (guard : d1 p = 1) : d1716 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15837 p hg
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15838 p hg
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15840 (p : Pattern) (guard : d1 p = 1) : d1717 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15835 p hg
    simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15839 p hg
    simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15841 (p : Pattern) (guard : d4474 p = 1) : d1718 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15840 p hg
    simpa only [d4474, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15842 (p : Pattern) (guard : d4475 p = 1) : d1809 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15832 p hg
    simpa only [d4475, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15841 p hg
    simpa only [d4475, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15843 (p : Pattern) (guard : d4475 p = 1) : d1815 p ≤ (2 : Int) + d4494 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1815, d4494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15773 p hg
    simpa only [d1815, d4494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1815, d4494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15842 p hg
    simpa only [d1815, d4494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15844 (p : Pattern) (guard : d4475 p = 1) : d1816 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15802 p hg
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15826 p hg
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15845 (p : Pattern) (guard : d4475 p = 1) : d1817 p ≤ (2 : Int) + d4495 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1817, d4495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15843 p hg
    simpa only [d1817, d4495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1817, d4495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15844 p hg
    simpa only [d1817, d4495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15846 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15847 (p : Pattern) (guard : d1 p = 1) : d329 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15848 (p : Pattern) (guard : d1 p = 1) : d1751 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1831 p hg
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15847 p hg
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15849 (p : Pattern) (guard : d1 p = 1) : d1752 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15848 p hg
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15847 p hg
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15850 (p : Pattern) (guard : d4474 p = 1) : d1753 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15849 p hg
    simpa only [d4474, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15851 (p : Pattern) (guard : d4475 p = 1) : d1754 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15846 p hg
    simpa only [d4475, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15850 p hg
    simpa only [d4475, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15852 (p : Pattern) (guard : d4475 p = 1) : d1818 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15802 p hg
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15851 p hg
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15853 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15854 (p : Pattern) (guard : d1 p = 1) : d327 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15855 (p : Pattern) (guard : d1 p = 1) : d1728 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1757 p hg
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15854 p hg
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15856 (p : Pattern) (guard : d1 p = 1) : d1729 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15855 p hg
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15854 p hg
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15857 (p : Pattern) (guard : d4474 p = 1) : d1730 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15856 p hg
    simpa only [d4474, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15858 (p : Pattern) (guard : d4475 p = 1) : d1756 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15853 p hg
    simpa only [d4475, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15857 p hg
    simpa only [d4475, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15859 (p : Pattern) (guard : d4475 p = 1) : d1757 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15858 p hg
    simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15860 (p : Pattern) (guard : d4475 p = 1) : d1819 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15852 p hg
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15859 p hg
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15861 (p : Pattern) (guard : d4475 p = 1) : d1820 p ≤ (2 : Int) + d4496 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1820, d4496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15845 p hg
    simpa only [d1820, d4496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1820, d4496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15860 p hg
    simpa only [d1820, d4496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15862 (p : Pattern) (guard : d0 p = 1) : d1823 p ≤ (2 : Int) + d4496 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15863 (p : Pattern) (guard : d4476 p = 1) : d1824 p ≤ (2 : Int) + d4496 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15861 p hg
    simpa only [d4476, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15862 p hg
    simpa only [d4476, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15864 (p : Pattern) (guard : d4476 p = 1) : d1825 p ≤ (2 : Int) + d5504 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1825, d5504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15831 p hg
    simpa only [d1825, d5504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1825, d5504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15863 p hg
    simpa only [d1825, d5504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15865 (p : Pattern) (guard : d4476 p = 1) : d1826 p ≤ (2 : Int) + d5505 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1826, d5505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15746 p hg
    simpa only [d1826, d5505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1826, d5505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15864 p hg
    simpa only [d1826, d5505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15866 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (2 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15867 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15785 p hg
    simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15786 p hg
    simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15868 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15785 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15869 (p : Pattern) (guard : d1 p = 1) : d356 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15868 p hg
    simpa only [d356, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d356, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15870 (p : Pattern) (guard : d1 p = 1) : d1802 p ≤ (2 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15867 p hg
    simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15869 p hg
    simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15871 (p : Pattern) (guard : d1 p = 1) : d1803 p ≤ (2 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15870 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15869 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15872 (p : Pattern) (guard : d4474 p = 1) : d1804 p ≤ (2 : Int) + d40 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15871 p hg
    simpa only [d4474, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15738 p hg
    simpa only [d4474, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15873 (p : Pattern) (guard : d4475 p = 1) : d1805 p ≤ (2 : Int) + d40 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15866 p hg
    simpa only [d4475, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15872 p hg
    simpa only [d4475, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15874 (p : Pattern) (guard : d4475 p = 1) : d1827 p ≤ (2 : Int) + d4486 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1827, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15873 p hg
    simpa only [d1827, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1827, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15858 p hg
    simpa only [d1827, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15875 (p : Pattern) (guard : d4475 p = 1) : d1828 p ≤ (2 : Int) + d4502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1828, d4502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15874 p hg
    simpa only [d1828, d4502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1828, d4502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15859 p hg
    simpa only [d1828, d4502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15876 (p : Pattern) (guard : d4475 p = 1) : d1829 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15859 p hg
    simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15877 (p : Pattern) (guard : d4475 p = 1) : d1830 p ≤ (2 : Int) + d4504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1830, d4504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15875 p hg
    simpa only [d1830, d4504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1830, d4504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15876 p hg
    simpa only [d1830, d4504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15878 (p : Pattern) (guard : d0 p = 1) : d1831 p ≤ (2 : Int) + d4504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15879 (p : Pattern) (guard : d4476 p = 1) : d1832 p ≤ (2 : Int) + d4504 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15877 p hg
    simpa only [d4476, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15878 p hg
    simpa only [d4476, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15880 (p : Pattern) (guard : d4475 p = 1) : d1831 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15876 p hg
    simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15881 (p : Pattern) (guard : d4476 p = 1) : d1833 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15880 p hg
    simpa only [d4476, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4476, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15882 (p : Pattern) (guard : d4476 p = 1) : d1834 p ≤ (2 : Int) + d5506 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1834, d5506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15879 p hg
    simpa only [d1834, d5506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1834, d5506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15881 p hg
    simpa only [d1834, d5506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15883 (p : Pattern) (guard : d4476 p = 1) : d1835 p ≤ (2 : Int) + d5507 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1835, d5507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15864 p hg
    simpa only [d1835, d5507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1835, d5507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15882 p hg
    simpa only [d1835, d5507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15884 (p : Pattern) (guard : d4476 p = 1) : d1836 p ≤ (2 : Int) + d5508 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1836, d5508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15865 p hg
    simpa only [d1836, d5508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1836, d5508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15883 p hg
    simpa only [d1836, d5508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15885 (p : Pattern) (guard : d4475 p = 1) : d1837 p ≤ (2 : Int) + d14 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15678 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15681 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15886 (p : Pattern) (guard : d4475 p = 1) : d1838 p ≤ (2 : Int) + d4478 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1838, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15885 p hg
    simpa only [d1838, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1838, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15691 p hg
    simpa only [d1838, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15887 (p : Pattern) (guard : d4475 p = 1) : d1839 p ≤ (2 : Int) + d4481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1839, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15886 p hg
    simpa only [d1839, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1839, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15704 p hg
    simpa only [d1839, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15888 (p : Pattern) (guard : d4476 p = 1) : d1840 p ≤ (2 : Int) + d4481 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15887 p hg
    simpa only [d4476, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15706 p hg
    simpa only [d4476, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15889 (p : Pattern) (guard : d4475 p = 1) : d1841 p ≤ (2 : Int) + d4482 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1841, d4482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15681 p hg
    simpa only [d1841, d4482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1841, d4482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15718 p hg
    simpa only [d1841, d4482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15890 (p : Pattern) (guard : d4475 p = 1) : d1842 p ≤ (2 : Int) + d4484 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1842, d4484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15889 p hg
    simpa only [d1842, d4484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1842, d4484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15720 p hg
    simpa only [d1842, d4484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15891 (p : Pattern) (guard : d4475 p = 1) : d1843 p ≤ (2 : Int) + d4488 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1843, d4488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15890 p hg
    simpa only [d1843, d4488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1843, d4488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15742 p hg
    simpa only [d1843, d4488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15892 (p : Pattern) (guard : d4476 p = 1) : d1844 p ≤ (2 : Int) + d4488 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15891 p hg
    simpa only [d4476, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15744 p hg
    simpa only [d4476, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15893 (p : Pattern) (guard : d4476 p = 1) : d1845 p ≤ (2 : Int) + d4489 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1845, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15888 p hg
    simpa only [d1845, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1845, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15892 p hg
    simpa only [d1845, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15894 (p : Pattern) (guard : d4476 p = 1) : d1846 p ≤ (2 : Int) + d5505 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1846, d5505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15893 p hg
    simpa only [d1846, d5505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1846, d5505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15864 p hg
    simpa only [d1846, d5505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15895 (p : Pattern) (guard : d4476 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare15896 (p : Pattern) (guard : d4476 p = 1) : d1847 p ≤ (2 : Int) + d5509 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1847, d5509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15864 p hg
    simpa only [d1847, d5509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1847, d5509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15895 p hg
    simpa only [d1847, d5509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15897 (p : Pattern) (guard : d4476 p = 1) : d1848 p ≤ (2 : Int) + d5510 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1848, d5510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15894 p hg
    simpa only [d1848, d5510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1848, d5510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15896 p hg
    simpa only [d1848, d5510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15898 (p : Pattern) (guard : d4476 p = 1) : d1849 p ≤ (2 : Int) + d5511 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1849, d5511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15884 p hg
    simpa only [d1849, d5511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1849, d5511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15897 p hg
    simpa only [d1849, d5511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15899 (p : Pattern) (guard : d0 p = 1) : d1850 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15900 (p : Pattern) (guard : d4475 p = 1) : d1851 p ≤ (2 : Int) + d14 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15899 p hg
    simpa only [d4475, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15675 p hg
    simpa only [d4475, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15901 (p : Pattern) (guard : d4475 p = 1) : d1852 p ≤ (2 : Int) + d14 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15900 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15681 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15902 (p : Pattern) (guard : d4475 p = 1) : d1853 p ≤ (2 : Int) + d4478 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1853, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15901 p hg
    simpa only [d1853, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1853, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15691 p hg
    simpa only [d1853, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15903 (p : Pattern) (guard : d4475 p = 1) : d1854 p ≤ (2 : Int) + d4481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1854, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15902 p hg
    simpa only [d1854, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1854, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15704 p hg
    simpa only [d1854, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15904 (p : Pattern) (guard : d4476 p = 1) : d1855 p ≤ (2 : Int) + d4481 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15903 p hg
    simpa only [d4476, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15706 p hg
    simpa only [d4476, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15905 (p : Pattern) (guard : d4475 p = 1) : d1856 p ≤ (2 : Int) + d4482 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1856, d4482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15678 p hg
    simpa only [d1856, d4482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1856, d4482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15718 p hg
    simpa only [d1856, d4482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15906 (p : Pattern) (guard : d4475 p = 1) : d1857 p ≤ (2 : Int) + d4484 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1857, d4484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15905 p hg
    simpa only [d1857, d4484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1857, d4484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15720 p hg
    simpa only [d1857, d4484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15907 (p : Pattern) (guard : d4475 p = 1) : d1858 p ≤ (2 : Int) + d4488 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1858, d4488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15906 p hg
    simpa only [d1858, d4488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1858, d4488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15742 p hg
    simpa only [d1858, d4488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15908 (p : Pattern) (guard : d4476 p = 1) : d1859 p ≤ (2 : Int) + d4488 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15907 p hg
    simpa only [d4476, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15744 p hg
    simpa only [d4476, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15909 (p : Pattern) (guard : d4476 p = 1) : d1860 p ≤ (2 : Int) + d4489 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1860, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15904 p hg
    simpa only [d1860, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1860, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15908 p hg
    simpa only [d1860, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15910 (p : Pattern) (guard : d4476 p = 1) : d1861 p ≤ (2 : Int) + d5505 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1861, d5505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15909 p hg
    simpa only [d1861, d5505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1861, d5505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15864 p hg
    simpa only [d1861, d5505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15911 (p : Pattern) (guard : d4476 p = 1) : d1862 p ≤ (2 : Int) + d5508 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1862, d5508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15910 p hg
    simpa only [d1862, d5508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1862, d5508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15883 p hg
    simpa only [d1862, d5508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15912 (p : Pattern) (guard : d4475 p = 1) : d1863 p ≤ (2 : Int) + d4478 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1863, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15681 p hg
    simpa only [d1863, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1863, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15691 p hg
    simpa only [d1863, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15913 (p : Pattern) (guard : d4475 p = 1) : d1864 p ≤ (2 : Int) + d4481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1864, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15912 p hg
    simpa only [d1864, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1864, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15704 p hg
    simpa only [d1864, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15914 (p : Pattern) (guard : d4476 p = 1) : d1865 p ≤ (2 : Int) + d4481 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15913 p hg
    simpa only [d4476, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15706 p hg
    simpa only [d4476, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15915 (p : Pattern) (guard : d4476 p = 1) : d1866 p ≤ (2 : Int) + d4489 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1866, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15914 p hg
    simpa only [d1866, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1866, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15892 p hg
    simpa only [d1866, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15916 (p : Pattern) (guard : d4476 p = 1) : d1867 p ≤ (2 : Int) + d5505 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1867, d5505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15915 p hg
    simpa only [d1867, d5505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1867, d5505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15864 p hg
    simpa only [d1867, d5505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15917 (p : Pattern) (guard : d4476 p = 1) : d1868 p ≤ (2 : Int) + d5510 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1868, d5510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15916 p hg
    simpa only [d1868, d5510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1868, d5510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15896 p hg
    simpa only [d1868, d5510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15918 (p : Pattern) (guard : d4476 p = 1) : d1869 p ≤ (2 : Int) + d5511 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1869, d5511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15911 p hg
    simpa only [d1869, d5511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1869, d5511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15917 p hg
    simpa only [d1869, d5511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15919 (p : Pattern) (guard : d4476 p = 1) : d1870 p ≤ (2 : Int) + d5511 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15898 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15918 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15920 (p : Pattern) (guard : d0 p = 1) : d1871 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15921 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d1 p := by
  omega
theorem compare15922 (p : Pattern) (guard : d1 p = 1) : d1872 p ≤ (2 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2157 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15923 (p : Pattern) (guard : d1 p = 1) : d1873 p ≤ (2 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1873, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15922 p hg
    simpa only [d1873, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1873, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2158 p hg
    simpa only [d1873, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15924 (p : Pattern) (guard : d1 p = 1) : d1874 p ≤ (2 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15923 p hg
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15925 (p : Pattern) (guard : d1 p = 1) : d1875 p ≤ (2 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15924 p hg
    simpa only [d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15923 p hg
    simpa only [d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15926 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15927 (p : Pattern) (guard : d4474 p = 1) : d1876 p ≤ (2 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15925 p hg
    simpa only [d4474, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15926 p hg
    simpa only [d4474, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15928 (p : Pattern) (guard : d4475 p = 1) : d1877 p ≤ (2 : Int) + d103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15920 p hg
    simpa only [d4475, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15927 p hg
    simpa only [d4475, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15929 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15930 (p : Pattern) (guard : d4475 p = 1) : d1878 p ≤ (2 : Int) + d103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15929 p hg
    simpa only [d4475, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15927 p hg
    simpa only [d4475, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15931 (p : Pattern) (guard : d4475 p = 1) : d1879 p ≤ (2 : Int) + d103 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15928 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15930 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15932 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (2 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15933 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d5 p := by
  omega
theorem compare15934 (p : Pattern) (guard : d1 p = 1) : d1880 p ≤ (2 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15935 (p : Pattern) (guard : d1 p = 1) : d1881 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1881, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15934 p hg
    simpa only [d1881, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1881, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d1881, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15936 (p : Pattern) (guard : d1 p = 1) : d1882 p ≤ (2 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15935 p hg
    simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15937 (p : Pattern) (guard : d1 p = 1) : d1883 p ≤ (2 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15936 p hg
    simpa only [d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15935 p hg
    simpa only [d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15938 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15939 (p : Pattern) (guard : d4474 p = 1) : d1884 p ≤ (2 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15937 p hg
    simpa only [d4474, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15938 p hg
    simpa only [d4474, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15940 (p : Pattern) (guard : d4475 p = 1) : d1885 p ≤ (2 : Int) + d107 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15932 p hg
    simpa only [d4475, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15939 p hg
    simpa only [d4475, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15941 (p : Pattern) (guard : d4475 p = 1) : d1886 p ≤ (2 : Int) + d4513 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1886, d4513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15930 p hg
    simpa only [d1886, d4513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1886, d4513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15940 p hg
    simpa only [d1886, d4513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15942 (p : Pattern) (guard : d4475 p = 1) : d1887 p ≤ (2 : Int) + d4514 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1887, d4514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15931 p hg
    simpa only [d1887, d4514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1887, d4514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15941 p hg
    simpa only [d1887, d4514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15943 (p : Pattern) (guard : d4475 p = 1) : d1888 p ≤ (2 : Int) + d4515 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1888, d4515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15730 p hg
    simpa only [d1888, d4515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1888, d4515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1888, d4515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15944 (p : Pattern) (guard : d4475 p = 1) : d1889 p ≤ (2 : Int) + d4516 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1889, d4516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15941 p hg
    simpa only [d1889, d4516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1889, d4516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15943 p hg
    simpa only [d1889, d4516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15945 (p : Pattern) (guard : d4475 p = 1) : d1890 p ≤ (2 : Int) + d4517 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1890, d4517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15942 p hg
    simpa only [d1890, d4517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1890, d4517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15944 p hg
    simpa only [d1890, d4517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15946 (p : Pattern) (guard : d0 p = 1) : d1914 p ≤ (2 : Int) + d4517 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15947 (p : Pattern) (guard : d4476 p = 1) : d1915 p ≤ (2 : Int) + d4517 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15945 p hg
    simpa only [d4476, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15946 p hg
    simpa only [d4476, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15948 (p : Pattern) (guard : d0 p = 1) : d1916 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15949 (p : Pattern) (guard : d4475 p = 1) : d1917 p ≤ (2 : Int) + d103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15948 p hg
    simpa only [d4475, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15927 p hg
    simpa only [d4475, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15950 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (2 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15951 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d3 p := by
  omega
theorem compare15952 (p : Pattern) (guard : d1 p = 1) : d1918 p ≤ (2 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2187 p hg
    simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15953 (p : Pattern) (guard : d1 p = 1) : d1919 p ≤ (2 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1919, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15952 p hg
    simpa only [d1919, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1919, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2188 p hg
    simpa only [d1919, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15954 (p : Pattern) (guard : d1 p = 1) : d1920 p ≤ (2 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15953 p hg
    simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15955 (p : Pattern) (guard : d1 p = 1) : d1921 p ≤ (2 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15954 p hg
    simpa only [d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15953 p hg
    simpa only [d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15956 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15957 (p : Pattern) (guard : d4474 p = 1) : d1922 p ≤ (2 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15955 p hg
    simpa only [d4474, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15956 p hg
    simpa only [d4474, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15958 (p : Pattern) (guard : d4475 p = 1) : d1923 p ≤ (2 : Int) + d116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15950 p hg
    simpa only [d4475, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15957 p hg
    simpa only [d4475, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15959 (p : Pattern) (guard : d4475 p = 1) : d1924 p ≤ (2 : Int) + d4518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1924, d4518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15949 p hg
    simpa only [d1924, d4518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1924, d4518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15958 p hg
    simpa only [d1924, d4518, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
