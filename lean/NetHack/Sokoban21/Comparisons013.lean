/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons012
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c1820 (pattern : Twelve) (guard : d1854 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1626 pattern := by
  omega
theorem c1821 (pattern : Twelve) (guard : d1855 pattern = 1) : d1699 pattern ≤ (0 : Int) + d1735 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1699, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1812 pattern childGuard
    simpa only [d1855, d1699, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1699, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1820 pattern childGuard
    simpa only [d1855, d1699, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1822 (pattern : Twelve) (guard : d1855 pattern = 1) : d1701 pattern ≤ (0 : Int) + d1739 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1701, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1819 pattern childGuard
    simpa only [d1701, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1701, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1821 pattern childGuard
    simpa only [d1701, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1823 (pattern : Twelve) (guard : d1855 pattern = 1) : d1703 pattern ≤ (0 : Int) + d1741 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1703, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1822 pattern childGuard
    simpa only [d1703, d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1703, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1816 pattern childGuard
    simpa only [d1703, d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1824 (pattern : Twelve) (guard : d1855 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1743 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1704, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1806 pattern childGuard
    simpa only [d1704, d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1704, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1823 pattern childGuard
    simpa only [d1704, d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1825 (pattern : Twelve) (guard : d1855 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1744 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1818 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1824 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1826 (pattern : Twelve) (guard : d1849 pattern = 1) : d235 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c810 pattern childGuard
    simpa only [d1849, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1827 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d26 pattern := by
  omega
theorem c1828 (pattern : Twelve) (guard : d1849 pattern = 1) : d236 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d236, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1827 pattern childGuard
    simpa only [d1849, d236, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d236, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c812 pattern childGuard
    simpa only [d1849, d236, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1829 (pattern : Twelve) (guard : d1849 pattern = 1) : d256 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d256, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1826 pattern childGuard
    simpa only [d256, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d256, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1828 pattern childGuard
    simpa only [d256, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1830 (pattern : Twelve) (guard : d1848 pattern = 1) : d28 pattern ≤ (0 : Int) + d28 pattern := by
  omega
theorem c1831 (pattern : Twelve) (guard : d1849 pattern = 1) : d238 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d238, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1830 pattern childGuard
    simpa only [d1849, d238, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d238, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c817 pattern childGuard
    simpa only [d1849, d238, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1832 (pattern : Twelve) (guard : d1849 pattern = 1) : d257 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d257, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1561 pattern childGuard
    simpa only [d257, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d257, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1831 pattern childGuard
    simpa only [d257, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1833 (pattern : Twelve) (guard : d1849 pattern = 1) : d272 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d272, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1829 pattern childGuard
    simpa only [d272, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d272, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1832 pattern childGuard
    simpa only [d272, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1834 (pattern : Twelve) (guard : d0 pattern = 1) : d273 pattern ≤ (0 : Int) + d208 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1835 (pattern : Twelve) (guard : d1857 pattern = 1) : d284 pattern ≤ (0 : Int) + d352 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d284, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1833 pattern childGuard
    simpa only [d1857, d284, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d284, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1834 pattern childGuard
    simpa only [d1857, d284, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1836 (pattern : Twelve) (guard : d1849 pattern = 1) : d242 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c833 pattern childGuard
    simpa only [d1849, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1837 (pattern : Twelve) (guard : d1849 pattern = 1) : d243 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d243, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1827 pattern childGuard
    simpa only [d1849, d243, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d243, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c835 pattern childGuard
    simpa only [d1849, d243, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1838 (pattern : Twelve) (guard : d1849 pattern = 1) : d260 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d260, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1836 pattern childGuard
    simpa only [d260, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d260, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1837 pattern childGuard
    simpa only [d260, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1839 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d1849, d241, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d241, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1840 (pattern : Twelve) (guard : d1849 pattern = 1) : d261 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d261, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1575 pattern childGuard
    simpa only [d261, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d261, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1839 pattern childGuard
    simpa only [d261, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1841 (pattern : Twelve) (guard : d1849 pattern = 1) : d274 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d274, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1838 pattern childGuard
    simpa only [d274, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d274, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1840 pattern childGuard
    simpa only [d274, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1842 (pattern : Twelve) (guard : d0 pattern = 1) : d275 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1843 (pattern : Twelve) (guard : d1857 pattern = 1) : d285 pattern ≤ (0 : Int) + d353 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d285, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1841 pattern childGuard
    simpa only [d1857, d285, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d285, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1842 pattern childGuard
    simpa only [d1857, d285, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1844 (pattern : Twelve) (guard : d1857 pattern = 1) : d293 pattern ≤ (0 : Int) + d358 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d293, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1835 pattern childGuard
    simpa only [d293, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d293, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1843 pattern childGuard
    simpa only [d293, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1845 (pattern : Twelve) (guard : d0 pattern = 1) : d180 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1846 (pattern : Twelve) (guard : d1849 pattern = 1) : d247 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d1849, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1845 pattern childGuard
    simpa only [d1849, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1847 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1848 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1847 pattern childGuard
    simpa only [d1848, d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1849 (pattern : Twelve) (guard : d0 pattern = 1) : d181 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1850 (pattern : Twelve) (guard : d1849 pattern = 1) : d248 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d248, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1848 pattern childGuard
    simpa only [d1849, d248, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d248, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1849 pattern childGuard
    simpa only [d1849, d248, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1851 (pattern : Twelve) (guard : d1849 pattern = 1) : d264 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d264, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1846 pattern childGuard
    simpa only [d264, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d264, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1850 pattern childGuard
    simpa only [d264, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1852 (pattern : Twelve) (guard : d0 pattern = 1) : d181 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1853 (pattern : Twelve) (guard : d1849 pattern = 1) : d248 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1854 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1855 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d34, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1854 pattern childGuard
    simpa only [d1848, d34, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1856 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1855 pattern childGuard
    simpa only [d1849, d241, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d241, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1857 (pattern : Twelve) (guard : d1849 pattern = 1) : d265 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d265, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1853 pattern childGuard
    simpa only [d265, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d265, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1856 pattern childGuard
    simpa only [d265, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1858 (pattern : Twelve) (guard : d1849 pattern = 1) : d276 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d276, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1851 pattern childGuard
    simpa only [d276, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d276, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1857 pattern childGuard
    simpa only [d276, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1859 (pattern : Twelve) (guard : d0 pattern = 1) : d277 pattern ≤ (0 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1860 (pattern : Twelve) (guard : d1857 pattern = 1) : d286 pattern ≤ (0 : Int) + d354 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d286, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1858 pattern childGuard
    simpa only [d1857, d286, d354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d286, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1859 pattern childGuard
    simpa only [d1857, d286, d354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1861 (pattern : Twelve) (guard : d0 pattern = 1) : d183 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1862 (pattern : Twelve) (guard : d1849 pattern = 1) : d252 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1861 pattern childGuard
    simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1863 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1848 pattern childGuard
    simpa only [d1849, d246, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c883 pattern childGuard
    simpa only [d1849, d246, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1864 (pattern : Twelve) (guard : d1849 pattern = 1) : d268 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d268, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1862 pattern childGuard
    simpa only [d268, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d268, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1863 pattern childGuard
    simpa only [d268, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1865 (pattern : Twelve) (guard : d1849 pattern = 1) : d263 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1611 pattern childGuard
    simpa only [d263, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1839 pattern childGuard
    simpa only [d263, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1866 (pattern : Twelve) (guard : d1849 pattern = 1) : d278 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d278, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1864 pattern childGuard
    simpa only [d278, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d278, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1865 pattern childGuard
    simpa only [d278, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1867 (pattern : Twelve) (guard : d1857 pattern = 1) : d287 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d287, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1866 pattern childGuard
    simpa only [d1857, d287, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d287, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d287, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1868 (pattern : Twelve) (guard : d1857 pattern = 1) : d294 pattern ≤ (0 : Int) + d359 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d294, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1860 pattern childGuard
    simpa only [d294, d359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d294, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1867 pattern childGuard
    simpa only [d294, d359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1869 (pattern : Twelve) (guard : d1857 pattern = 1) : d297 pattern ≤ (0 : Int) + d361 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d297, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1844 pattern childGuard
    simpa only [d297, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d297, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1868 pattern childGuard
    simpa only [d297, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1870 (pattern : Twelve) (guard : d1849 pattern = 1) : d254 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d254, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1827 pattern childGuard
    simpa only [d1849, d254, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d254, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c883 pattern childGuard
    simpa only [d1849, d254, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1871 (pattern : Twelve) (guard : d1849 pattern = 1) : d269 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d269, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1636 pattern childGuard
    simpa only [d269, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d269, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1870 pattern childGuard
    simpa only [d269, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1872 (pattern : Twelve) (guard : d1849 pattern = 1) : d263 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1625 pattern childGuard
    simpa only [d263, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1839 pattern childGuard
    simpa only [d263, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1873 (pattern : Twelve) (guard : d1849 pattern = 1) : d279 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d279, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1871 pattern childGuard
    simpa only [d279, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d279, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1872 pattern childGuard
    simpa only [d279, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1874 (pattern : Twelve) (guard : d0 pattern = 1) : d280 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1875 (pattern : Twelve) (guard : d1857 pattern = 1) : d288 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d288, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1873 pattern childGuard
    simpa only [d1857, d288, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d288, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1874 pattern childGuard
    simpa only [d1857, d288, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1876 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1611 pattern childGuard
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1863 pattern childGuard
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1877 (pattern : Twelve) (guard : d1849 pattern = 1) : d280 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d280, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1876 pattern childGuard
    simpa only [d280, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d280, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1872 pattern childGuard
    simpa only [d280, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1878 (pattern : Twelve) (guard : d0 pattern = 1) : d281 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1879 (pattern : Twelve) (guard : d1857 pattern = 1) : d289 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d289, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1877 pattern childGuard
    simpa only [d1857, d289, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d289, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1878 pattern childGuard
    simpa only [d1857, d289, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1880 (pattern : Twelve) (guard : d1857 pattern = 1) : d290 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d290, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1877 pattern childGuard
    simpa only [d1857, d290, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d290, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d290, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1881 (pattern : Twelve) (guard : d1857 pattern = 1) : d295 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1879 pattern childGuard
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1880 pattern childGuard
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1882 (pattern : Twelve) (guard : d1857 pattern = 1) : d298 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1875 pattern childGuard
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1881 pattern childGuard
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1883 (pattern : Twelve) (guard : d1857 pattern = 1) : d300 pattern ≤ (0 : Int) + d362 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d300, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1869 pattern childGuard
    simpa only [d300, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d300, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1882 pattern childGuard
    simpa only [d300, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1884 (pattern : Twelve) (guard : d1849 pattern = 1) : d255 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d255, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1830 pattern childGuard
    simpa only [d1849, d255, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d255, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d255, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1885 (pattern : Twelve) (guard : d1849 pattern = 1) : d270 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d270, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1636 pattern childGuard
    simpa only [d270, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d270, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1884 pattern childGuard
    simpa only [d270, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1886 (pattern : Twelve) (guard : d1849 pattern = 1) : d282 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d282, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1871 pattern childGuard
    simpa only [d282, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d282, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1885 pattern childGuard
    simpa only [d282, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1887 (pattern : Twelve) (guard : d1857 pattern = 1) : d291 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d291, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1886 pattern childGuard
    simpa only [d1857, d291, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d291, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1874 pattern childGuard
    simpa only [d1857, d291, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1888 (pattern : Twelve) (guard : d1849 pattern = 1) : d271 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d271, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1636 pattern childGuard
    simpa only [d271, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d271, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1839 pattern childGuard
    simpa only [d271, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1889 (pattern : Twelve) (guard : d1849 pattern = 1) : d283 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d283, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1871 pattern childGuard
    simpa only [d283, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d283, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1888 pattern childGuard
    simpa only [d283, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1890 (pattern : Twelve) (guard : d1857 pattern = 1) : d292 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d292, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1889 pattern childGuard
    simpa only [d1857, d292, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d292, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1874 pattern childGuard
    simpa only [d1857, d292, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1891 (pattern : Twelve) (guard : d1857 pattern = 1) : d296 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d296, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1887 pattern childGuard
    simpa only [d296, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d296, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1890 pattern childGuard
    simpa only [d296, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1892 (pattern : Twelve) (guard : d1849 pattern = 1) : d263 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1611 pattern childGuard
    simpa only [d263, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1856 pattern childGuard
    simpa only [d263, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1893 (pattern : Twelve) (guard : d1849 pattern = 1) : d280 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d280, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1876 pattern childGuard
    simpa only [d280, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d280, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1892 pattern childGuard
    simpa only [d280, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1894 (pattern : Twelve) (guard : d1857 pattern = 1) : d289 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d289, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1893 pattern childGuard
    simpa only [d1857, d289, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d289, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1878 pattern childGuard
    simpa only [d1857, d289, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1895 (pattern : Twelve) (guard : d1849 pattern = 1) : d280 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d280, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1876 pattern childGuard
    simpa only [d280, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d280, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1865 pattern childGuard
    simpa only [d280, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1896 (pattern : Twelve) (guard : d1857 pattern = 1) : d290 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d290, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1895 pattern childGuard
    simpa only [d1857, d290, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d290, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d290, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1897 (pattern : Twelve) (guard : d1857 pattern = 1) : d295 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d295, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1894 pattern childGuard
    simpa only [d295, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d295, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1896 pattern childGuard
    simpa only [d295, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1898 (pattern : Twelve) (guard : d1857 pattern = 1) : d299 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1891 pattern childGuard
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1897 pattern childGuard
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1899 (pattern : Twelve) (guard : d1857 pattern = 1) : d301 pattern ≤ (0 : Int) + d363 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d301, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1898 pattern childGuard
    simpa only [d301, d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d301, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1882 pattern childGuard
    simpa only [d301, d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1900 (pattern : Twelve) (guard : d1857 pattern = 1) : d302 pattern ≤ (0 : Int) + d364 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d302, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1883 pattern childGuard
    simpa only [d302, d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d302, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1899 pattern childGuard
    simpa only [d302, d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1901 (pattern : Twelve) (guard : d1857 pattern = 1) : d303 pattern ≤ (0 : Int) + d365 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d303, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1900 pattern childGuard
    simpa only [d303, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d303, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1899 pattern childGuard
    simpa only [d303, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1902 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d27 pattern := by
  omega
theorem c1903 (pattern : Twelve) (guard : d1849 pattern = 1) : d940 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d940, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1902 pattern childGuard
    simpa only [d1849, d940, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d940, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c960 pattern childGuard
    simpa only [d1849, d940, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1904 (pattern : Twelve) (guard : d1849 pattern = 1) : d947 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d947, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1561 pattern childGuard
    simpa only [d947, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d947, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1903 pattern childGuard
    simpa only [d947, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1905 (pattern : Twelve) (guard : d1849 pattern = 1) : d942 pattern ≤ (0 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d1849, d942, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1849, d942, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1906 (pattern : Twelve) (guard : d1849 pattern = 1) : d948 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d948, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1671 pattern childGuard
    simpa only [d948, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d948, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1905 pattern childGuard
    simpa only [d948, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1907 (pattern : Twelve) (guard : d1849 pattern = 1) : d955 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d955, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1904 pattern childGuard
    simpa only [d955, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d955, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1906 pattern childGuard
    simpa only [d955, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1908 (pattern : Twelve) (guard : d0 pattern = 1) : d956 pattern ≤ (0 : Int) + d913 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1909 (pattern : Twelve) (guard : d1857 pattern = 1) : d963 pattern ≤ (0 : Int) + d1018 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d963, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1907 pattern childGuard
    simpa only [d1857, d963, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d963, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1908 pattern childGuard
    simpa only [d1857, d963, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1910 (pattern : Twelve) (guard : d1849 pattern = 1) : d943 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d943, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1902 pattern childGuard
    simpa only [d1849, d943, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d943, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c977 pattern childGuard
    simpa only [d1849, d943, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1911 (pattern : Twelve) (guard : d1849 pattern = 1) : d950 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d950, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1575 pattern childGuard
    simpa only [d950, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d950, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1910 pattern childGuard
    simpa only [d950, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1912 (pattern : Twelve) (guard : d1849 pattern = 1) : d951 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d951, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1684 pattern childGuard
    simpa only [d951, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d951, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1905 pattern childGuard
    simpa only [d951, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1913 (pattern : Twelve) (guard : d1849 pattern = 1) : d957 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d957, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1911 pattern childGuard
    simpa only [d957, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d957, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1912 pattern childGuard
    simpa only [d957, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1914 (pattern : Twelve) (guard : d0 pattern = 1) : d958 pattern ≤ (0 : Int) + d914 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1915 (pattern : Twelve) (guard : d1857 pattern = 1) : d964 pattern ≤ (0 : Int) + d1019 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d964, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1913 pattern childGuard
    simpa only [d1857, d964, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d964, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1914 pattern childGuard
    simpa only [d1857, d964, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1916 (pattern : Twelve) (guard : d1857 pattern = 1) : d970 pattern ≤ (0 : Int) + d1023 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d970, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1909 pattern childGuard
    simpa only [d970, d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d970, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1915 pattern childGuard
    simpa only [d970, d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1917 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1918 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d34, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1917 pattern childGuard
    simpa only [d1848, d34, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1919 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1918 pattern childGuard
    simpa only [d1849, d241, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c977 pattern childGuard
    simpa only [d1849, d241, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1920 (pattern : Twelve) (guard : d1849 pattern = 1) : d265 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d265, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1853 pattern childGuard
    simpa only [d265, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d265, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1919 pattern childGuard
    simpa only [d265, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1921 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1922 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1921 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1923 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1922 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c980 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1924 (pattern : Twelve) (guard : d1849 pattern = 1) : d949 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d949, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1923 pattern childGuard
    simpa only [d949, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d949, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1905 pattern childGuard
    simpa only [d949, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1925 (pattern : Twelve) (guard : d1849 pattern = 1) : d959 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d959, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1920 pattern childGuard
    simpa only [d959, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d959, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1924 pattern childGuard
    simpa only [d959, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1926 (pattern : Twelve) (guard : d0 pattern = 1) : d960 pattern ≤ (0 : Int) + d916 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1927 (pattern : Twelve) (guard : d1857 pattern = 1) : d965 pattern ≤ (0 : Int) + d1020 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d965, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1925 pattern childGuard
    simpa only [d1857, d965, d1020, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d965, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1926 pattern childGuard
    simpa only [d1857, d965, d1020, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1928 (pattern : Twelve) (guard : d1849 pattern = 1) : d263 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1611 pattern childGuard
    simpa only [d263, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1919 pattern childGuard
    simpa only [d263, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1929 (pattern : Twelve) (guard : d1849 pattern = 1) : d958 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d958, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1928 pattern childGuard
    simpa only [d958, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d958, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1924 pattern childGuard
    simpa only [d958, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1930 (pattern : Twelve) (guard : d1857 pattern = 1) : d966 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d966, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1929 pattern childGuard
    simpa only [d1857, d966, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d966, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d966, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1931 (pattern : Twelve) (guard : d1857 pattern = 1) : d971 pattern ≤ (0 : Int) + d1024 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d971, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1927 pattern childGuard
    simpa only [d971, d1024, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d971, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1930 pattern childGuard
    simpa only [d971, d1024, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1932 (pattern : Twelve) (guard : d1857 pattern = 1) : d973 pattern ≤ (0 : Int) + d1025 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d973, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1916 pattern childGuard
    simpa only [d973, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d973, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1931 pattern childGuard
    simpa only [d973, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1933 (pattern : Twelve) (guard : d1849 pattern = 1) : d953 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d953, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1636 pattern childGuard
    simpa only [d953, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d953, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1910 pattern childGuard
    simpa only [d953, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1934 (pattern : Twelve) (guard : d1848 pattern = 1) : d823 pattern ≤ (0 : Int) + d823 pattern := by
  omega
theorem c1935 (pattern : Twelve) (guard : d1849 pattern = 1) : d946 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1934 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1008 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1936 (pattern : Twelve) (guard : d1849 pattern = 1) : d954 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d954, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1935 pattern childGuard
    simpa only [d954, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d954, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1905 pattern childGuard
    simpa only [d954, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1937 (pattern : Twelve) (guard : d1849 pattern = 1) : d961 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d961, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1933 pattern childGuard
    simpa only [d961, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d961, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1936 pattern childGuard
    simpa only [d961, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1938 (pattern : Twelve) (guard : d0 pattern = 1) : d958 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1939 (pattern : Twelve) (guard : d1857 pattern = 1) : d967 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d967, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d1857, d967, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d967, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1938 pattern childGuard
    simpa only [d1857, d967, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1940 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1941 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d34, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1940 pattern childGuard
    simpa only [d1848, d34, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1942 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1941 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1008 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1943 (pattern : Twelve) (guard : d1849 pattern = 1) : d949 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d949, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1942 pattern childGuard
    simpa only [d949, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d949, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1905 pattern childGuard
    simpa only [d949, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1944 (pattern : Twelve) (guard : d1849 pattern = 1) : d958 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d958, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1928 pattern childGuard
    simpa only [d958, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d958, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1943 pattern childGuard
    simpa only [d958, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1945 (pattern : Twelve) (guard : d0 pattern = 1) : d960 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1946 (pattern : Twelve) (guard : d1857 pattern = 1) : d968 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d968, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1944 pattern childGuard
    simpa only [d1857, d968, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d968, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1945 pattern childGuard
    simpa only [d1857, d968, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1947 (pattern : Twelve) (guard : d1857 pattern = 1) : d966 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d966, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1944 pattern childGuard
    simpa only [d1857, d966, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d966, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d966, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1948 (pattern : Twelve) (guard : d1857 pattern = 1) : d972 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1946 pattern childGuard
    simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1947 pattern childGuard
    simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1949 (pattern : Twelve) (guard : d1857 pattern = 1) : d974 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1939 pattern childGuard
    simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1948 pattern childGuard
    simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1950 (pattern : Twelve) (guard : d1857 pattern = 1) : d976 pattern ≤ (0 : Int) + d1026 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d976, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1932 pattern childGuard
    simpa only [d976, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d976, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1949 pattern childGuard
    simpa only [d976, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1951 (pattern : Twelve) (guard : d1849 pattern = 1) : d962 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d962, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1933 pattern childGuard
    simpa only [d962, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d962, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1912 pattern childGuard
    simpa only [d962, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1952 (pattern : Twelve) (guard : d1857 pattern = 1) : d969 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d969, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1951 pattern childGuard
    simpa only [d1857, d969, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d969, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1938 pattern childGuard
    simpa only [d1857, d969, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1953 (pattern : Twelve) (guard : d1857 pattern = 1) : d968 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d968, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1929 pattern childGuard
    simpa only [d1857, d968, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d968, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1945 pattern childGuard
    simpa only [d1857, d968, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1954 (pattern : Twelve) (guard : d1857 pattern = 1) : d972 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1953 pattern childGuard
    simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1930 pattern childGuard
    simpa only [d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1955 (pattern : Twelve) (guard : d1857 pattern = 1) : d975 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1952 pattern childGuard
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1954 pattern childGuard
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1956 (pattern : Twelve) (guard : d1857 pattern = 1) : d977 pattern ≤ (0 : Int) + d1027 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d977, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1955 pattern childGuard
    simpa only [d977, d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d977, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1949 pattern childGuard
    simpa only [d977, d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1957 (pattern : Twelve) (guard : d1857 pattern = 1) : d978 pattern ≤ (0 : Int) + d1028 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d978, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1950 pattern childGuard
    simpa only [d978, d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d978, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1956 pattern childGuard
    simpa only [d978, d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1958 (pattern : Twelve) (guard : d1857 pattern = 1) : d979 pattern ≤ (0 : Int) + d1029 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d979, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1957 pattern childGuard
    simpa only [d979, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d979, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1956 pattern childGuard
    simpa only [d979, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1959 (pattern : Twelve) (guard : d1848 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1278 pattern := by
  omega
end NetHack.Sokoban21.Diagram
