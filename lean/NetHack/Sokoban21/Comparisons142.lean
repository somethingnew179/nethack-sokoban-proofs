/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons141
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c19880 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19873 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19881 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19879 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19880 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19882 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19878 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19881 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19883 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19704 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19666 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19884 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19883 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19885 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19882 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19884 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19886 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19876 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19885 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19887 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19665 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19879 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19888 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19704 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19889 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19887 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19888 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19890 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19481 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19891 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19481 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19892 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19890 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19891 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19893 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19883 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19892 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19894 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19705 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19895 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19893 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19894 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19896 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19889 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19895 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19897 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19885 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19898 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19896 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19897 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19899 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19886 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19898 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19900 (pattern : Twelve) (guard : d1872 pattern = 1) : d1664 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19872 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19899 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19901 (pattern : Twelve) (guard : d0 pattern = 1) : d1677 pattern ≤ (16 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c19902 (pattern : Twelve) (guard : d1 pattern = 1) : d1814 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19664 pattern childGuard
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19481 pattern childGuard
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19903 (pattern : Twelve) (guard : d1 pattern = 1) : d1815 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19491 pattern childGuard
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19904 (pattern : Twelve) (guard : d1 pattern = 1) : d1818 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19902 pattern childGuard
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19903 pattern childGuard
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19905 (pattern : Twelve) (guard : d1 pattern = 1) : d1821 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19904 pattern childGuard
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19895 pattern childGuard
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19906 (pattern : Twelve) (guard : d1 pattern = 1) : d1816 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19704 pattern childGuard
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19890 pattern childGuard
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19907 (pattern : Twelve) (guard : d1 pattern = 1) : d1819 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19906 pattern childGuard
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19894 pattern childGuard
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19908 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19909 (pattern : Twelve) (guard : d1 pattern = 1) : d1817 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19705 pattern childGuard
    simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19908 pattern childGuard
    simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19910 (pattern : Twelve) (guard : d1 pattern = 1) : d1820 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19909 pattern childGuard
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19911 (pattern : Twelve) (guard : d1 pattern = 1) : d1822 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19907 pattern childGuard
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19910 pattern childGuard
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19912 (pattern : Twelve) (guard : d1 pattern = 1) : d1823 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19895 pattern childGuard
    simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19913 (pattern : Twelve) (guard : d1 pattern = 1) : d1824 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19911 pattern childGuard
    simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19912 pattern childGuard
    simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19914 (pattern : Twelve) (guard : d1 pattern = 1) : d1825 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19905 pattern childGuard
    simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19913 pattern childGuard
    simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19915 (pattern : Twelve) (guard : d1872 pattern = 1) : d1826 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19901 pattern childGuard
    simpa only [d1872, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19914 pattern childGuard
    simpa only [d1872, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19916 (pattern : Twelve) (guard : d1872 pattern = 1) : d1827 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19900 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19915 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19917 (pattern : Twelve) (guard : d1872 pattern = 1) : d156 pattern ≤ (0 : Int) + d156 pattern := by
  omega
theorem c19918 (pattern : Twelve) (guard : d1872 pattern = 1) : d907 pattern ≤ (0 : Int) + d907 pattern := by
  omega
theorem c19919 (pattern : Twelve) (guard : d1872 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1354 pattern := by
  omega
theorem c19920 (pattern : Twelve) (guard : d1872 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1678 pattern := by
  omega
theorem c19921 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (16 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19778 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19464 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19922 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (16 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19921 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19923 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (16 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19922 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19471 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19924 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (16 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19923 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19925 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (16 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19448 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19924 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19926 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (16 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19445 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19491 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19927 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (16 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19926 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19928 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (16 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19483 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19927 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19929 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (16 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19930 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (16 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19929 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19931 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (16 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19930 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19472 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19932 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (16 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19928 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19931 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19933 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (16 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19925 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19932 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19934 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (16 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19472 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19935 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (16 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19448 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19934 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19936 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (16 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19445 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19937 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (16 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19936 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19938 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (16 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19503 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19937 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19939 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (16 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19671 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19472 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19940 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (16 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19938 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19939 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19941 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (16 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19935 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19940 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19942 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (16 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19933 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19941 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19943 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (16 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19445 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19944 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (16 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19943 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19945 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (16 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19475 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19944 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19946 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (16 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19472 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19947 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (16 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19945 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19946 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19948 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (16 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19462 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19949 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (16 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19484 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19948 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19950 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (16 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19949 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19951 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (16 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19950 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19952 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (16 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19525 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19951 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19953 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (16 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19798 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19954 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (16 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19542 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19953 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19955 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (16 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19696 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19954 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19956 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (16 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19952 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19955 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19957 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (16 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19947 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19956 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19958 (pattern : Twelve) (guard : d1 pattern = 1) : d105 pattern ≤ (16 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19940 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19959 (pattern : Twelve) (guard : d1 pattern = 1) : d111 pattern ≤ (16 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19957 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19958 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19960 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (16 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19942 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19959 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19961 (pattern : Twelve) (guard : d1872 pattern = 1) : d114 pattern ≤ (16 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19437 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19960 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19962 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (16 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19648 pattern childGuard
    simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19963 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (16 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19445 pattern childGuard
    simpa only [d27, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19648 pattern childGuard
    simpa only [d27, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19964 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (16 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19962 pattern childGuard
    simpa only [d50, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19963 pattern childGuard
    simpa only [d50, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19965 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (16 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19438 pattern childGuard
    simpa only [d72, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19964 pattern childGuard
    simpa only [d72, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19966 (pattern : Twelve) (guard : d1 pattern = 1) : d120 pattern ≤ (16 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d120, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d120, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d120, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19798 pattern childGuard
    simpa only [d120, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19967 (pattern : Twelve) (guard : d1 pattern = 1) : d129 pattern ≤ (16 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19966 pattern childGuard
    simpa only [d129, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19471 pattern childGuard
    simpa only [d129, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19968 (pattern : Twelve) (guard : d1 pattern = 1) : d136 pattern ≤ (16 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d136, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d136, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d136, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19967 pattern childGuard
    simpa only [d136, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19969 (pattern : Twelve) (guard : d1 pattern = 1) : d144 pattern ≤ (16 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d144, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19965 pattern childGuard
    simpa only [d144, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d144, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19968 pattern childGuard
    simpa only [d144, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19970 (pattern : Twelve) (guard : d1 pattern = 1) : d121 pattern ≤ (16 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d121, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d121, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d121, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19949 pattern childGuard
    simpa only [d121, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19971 (pattern : Twelve) (guard : d1 pattern = 1) : d130 pattern ≤ (16 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19970 pattern childGuard
    simpa only [d130, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19936 pattern childGuard
    simpa only [d130, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19972 (pattern : Twelve) (guard : d1 pattern = 1) : d137 pattern ≤ (16 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d137, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19483 pattern childGuard
    simpa only [d137, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d137, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19971 pattern childGuard
    simpa only [d137, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19973 (pattern : Twelve) (guard : d1 pattern = 1) : d138 pattern ≤ (16 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d138, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19671 pattern childGuard
    simpa only [d138, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d138, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19967 pattern childGuard
    simpa only [d138, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19974 (pattern : Twelve) (guard : d1 pattern = 1) : d145 pattern ≤ (16 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19972 pattern childGuard
    simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19973 pattern childGuard
    simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19975 (pattern : Twelve) (guard : d1 pattern = 1) : d149 pattern ≤ (16 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19969 pattern childGuard
    simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19974 pattern childGuard
    simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19976 (pattern : Twelve) (guard : d1 pattern = 1) : d139 pattern ≤ (16 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19503 pattern childGuard
    simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19971 pattern childGuard
    simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19977 (pattern : Twelve) (guard : d1 pattern = 1) : d146 pattern ≤ (16 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19976 pattern childGuard
    simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19973 pattern childGuard
    simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19978 (pattern : Twelve) (guard : d1 pattern = 1) : d150 pattern ≤ (16 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19969 pattern childGuard
    simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19977 pattern childGuard
    simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19979 (pattern : Twelve) (guard : d1 pattern = 1) : d153 pattern ≤ (16 : Int) + d902 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19975 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19978 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19980 (pattern : Twelve) (guard : d1 pattern = 1) : d122 pattern ≤ (16 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19445 pattern childGuard
    simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19529 pattern childGuard
    simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19981 (pattern : Twelve) (guard : d1 pattern = 1) : d131 pattern ≤ (16 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19970 pattern childGuard
    simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19980 pattern childGuard
    simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19982 (pattern : Twelve) (guard : d1 pattern = 1) : d140 pattern ≤ (16 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19475 pattern childGuard
    simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19981 pattern childGuard
    simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19983 (pattern : Twelve) (guard : d1 pattern = 1) : d123 pattern ≤ (16 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19685 pattern childGuard
    simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19984 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (16 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19983 pattern childGuard
    simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19985 (pattern : Twelve) (guard : d1 pattern = 1) : d141 pattern ≤ (16 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19984 pattern childGuard
    simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19967 pattern childGuard
    simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19986 (pattern : Twelve) (guard : d1 pattern = 1) : d147 pattern ≤ (16 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19982 pattern childGuard
    simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19985 pattern childGuard
    simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19987 (pattern : Twelve) (guard : d1 pattern = 1) : d124 pattern ≤ (16 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19852 pattern childGuard
    simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19988 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (16 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19672 pattern childGuard
    simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19527 pattern childGuard
    simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19989 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (16 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19684 pattern childGuard
    simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19988 pattern childGuard
    simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19990 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (16 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19989 pattern childGuard
    simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19991 (pattern : Twelve) (guard : d1 pattern = 1) : d133 pattern ≤ (16 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19987 pattern childGuard
    simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19990 pattern childGuard
    simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19992 (pattern : Twelve) (guard : d1 pattern = 1) : d142 pattern ≤ (16 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19525 pattern childGuard
    simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19991 pattern childGuard
    simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19993 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19589 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19744 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19994 (pattern : Twelve) (guard : d1 pattern = 1) : d126 pattern ≤ (16 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19993 pattern childGuard
    simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19995 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (16 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19994 pattern childGuard
    simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19699 pattern childGuard
    simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19996 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (16 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19465 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19997 (pattern : Twelve) (guard : d1 pattern = 1) : d135 pattern ≤ (16 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19996 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19891 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19998 (pattern : Twelve) (guard : d1 pattern = 1) : d143 pattern ≤ (16 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19995 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19997 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19999 (pattern : Twelve) (guard : d1 pattern = 1) : d148 pattern ≤ (16 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19992 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19998 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20000 (pattern : Twelve) (guard : d1 pattern = 1) : d151 pattern ≤ (16 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19986 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19999 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20001 (pattern : Twelve) (guard : d1 pattern = 1) : d152 pattern ≤ (16 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19977 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20002 (pattern : Twelve) (guard : d1 pattern = 1) : d154 pattern ≤ (16 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20000 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20001 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20003 (pattern : Twelve) (guard : d1 pattern = 1) : d155 pattern ≤ (16 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19979 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20002 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20004 (pattern : Twelve) (guard : d1872 pattern = 1) : d155 pattern ≤ (16 : Int) + d906 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19552 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20003 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20005 (pattern : Twelve) (guard : d1872 pattern = 1) : d156 pattern ≤ (16 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1872 pattern = 1 := by simpa only [d156, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19961 pattern childGuard
    simpa only [d156, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1872 pattern = 1 := by simpa only [d156, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20004 pattern childGuard
    simpa only [d156, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20006 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (16 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20007 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (16 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19653 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20006 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20008 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (16 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19650 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20009 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (16 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19675 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20008 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20010 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (16 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19671 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20009 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20011 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (16 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19789 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20012 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (16 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20010 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20011 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20013 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (16 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20007 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20012 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20014 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (16 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19650 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19685 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20015 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (16 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19675 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20014 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20016 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (16 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20015 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20017 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (16 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20018 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (16 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20016 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20017 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20019 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (16 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19948 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19684 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
