/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1820 (p : Pattern) (guard : d4059 p = 1) : d493 p ≤ (2 : Int) + d167 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d4059, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d4059, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4059, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1819 p hg
    simpa only [d4059, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1821 (p : Pattern) (guard : d4059 p = 1) : d494 p ≤ (2 : Int) + d4054 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4059 p = 1 := by simpa only [d494, d4054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1722 p hg
    simpa only [d494, d4054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4059 p = 1 := by simpa only [d494, d4054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1820 p hg
    simpa only [d494, d4054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1822 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d12 p := by
  change (9 : Int) ≤ (2 : Int) + 12
  decide
theorem compare1823 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1824 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1825 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1826 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1825 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1827 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1733 p hg
    simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1828 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1771 p hg
    simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1827 p hg
    simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1829 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d12 p := by
  change (10 : Int) ≤ (2 : Int) + 12
  decide
theorem compare1830 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1831 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1832 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1831 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1833 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1831 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1832 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1834 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1733 p hg
    simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1833 p hg
    simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1835 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (2 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1834 p hg
    simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1836 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1828 p hg
    simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1835 p hg
    simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1837 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1838 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (2 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1837 p hg
    simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1839 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (2 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1785 p hg
    simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1838 p hg
    simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1840 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1831 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1841 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (2 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1840 p hg
    simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1842 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (2 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1841 p hg
    simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1791 p hg
    simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1843 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (2 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1839 p hg
    simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1842 p hg
    simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1844 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (2 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1836 p hg
    simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1843 p hg
    simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1845 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (2 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1769 p hg
    simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1844 p hg
    simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1846 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (2 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1836 p hg
    simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1803 p hg
    simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1847 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1800 p hg
    simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1846 p hg
    simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1848 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (2 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1845 p hg
    simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1847 p hg
    simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1849 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (2 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1847 p hg
    simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1814 p hg
    simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1850 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (2 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1848 p hg
    simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1849 p hg
    simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1851 (p : Pattern) (guard : d0 p = 1) : d426 p ≤ (2 : Int) + d308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1852 (p : Pattern) (guard : d4058 p = 1) : d489 p ≤ (2 : Int) + d309 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d489, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1850 p hg
    simpa only [d4058, d489, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d489, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1851 p hg
    simpa only [d4058, d489, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1853 (p : Pattern) (guard : d0 p = 1) : d495 p ≤ (2 : Int) + d309 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1854 (p : Pattern) (guard : d4059 p = 1) : d496 p ≤ (2 : Int) + d309 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d4059, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1852 p hg
    simpa only [d4059, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4059, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1853 p hg
    simpa only [d4059, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1855 (p : Pattern) (guard : d4059 p = 1) : d497 p ≤ (2 : Int) + d4109 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4059 p = 1 := by simpa only [d497, d4109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1722 p hg
    simpa only [d497, d4109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4059 p = 1 := by simpa only [d497, d4109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1854 p hg
    simpa only [d497, d4109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1856 (p : Pattern) (guard : d4059 p = 1) : d498 p ≤ (2 : Int) + d4110 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4059 p = 1 := by simpa only [d498, d4110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1821 p hg
    simpa only [d498, d4110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4059 p = 1 := by simpa only [d498, d4110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1855 p hg
    simpa only [d498, d4110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1857 (p : Pattern) (guard : d0 p = 1) : d426 p ≤ (0 : Int) + d500 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1858 (p : Pattern) (guard : d4111 p = 1) : d489 p ≤ (0 : Int) + d501 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d4111, d489, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1120 p hg
    simpa only [d4111, d489, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4111, d489, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1857 p hg
    simpa only [d4111, d489, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1859 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (0 : Int) + d503 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1860 (p : Pattern) (guard : d4111 p = 1) : d490 p ≤ (0 : Int) + d504 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d4111, d490, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1125 p hg
    simpa only [d4111, d490, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4111, d490, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1859 p hg
    simpa only [d4111, d490, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1861 (p : Pattern) (guard : d4111 p = 1) : d491 p ≤ (0 : Int) + d505 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d491, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1858 p hg
    simpa only [d491, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d491, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1860 p hg
    simpa only [d491, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1862 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (0 : Int) + d507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1863 (p : Pattern) (guard : d4111 p = 1) : d492 p ≤ (0 : Int) + d508 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d4111, d492, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d4111, d492, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4111, d492, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1862 p hg
    simpa only [d4111, d492, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1864 (p : Pattern) (guard : d4111 p = 1) : d493 p ≤ (0 : Int) + d509 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d493, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1858 p hg
    simpa only [d493, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d493, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1863 p hg
    simpa only [d493, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1865 (p : Pattern) (guard : d4111 p = 1) : d494 p ≤ (0 : Int) + d510 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d494, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1861 p hg
    simpa only [d494, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d494, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1864 p hg
    simpa only [d494, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1866 (p : Pattern) (guard : d0 p = 1) : d477 p ≤ (0 : Int) + d512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1867 (p : Pattern) (guard : d4111 p = 1) : d495 p ≤ (0 : Int) + d513 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d4111, d495, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d4111, d495, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4111, d495, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1866 p hg
    simpa only [d4111, d495, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1868 (p : Pattern) (guard : d4111 p = 1) : d496 p ≤ (0 : Int) + d514 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d496, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1858 p hg
    simpa only [d496, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d496, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1867 p hg
    simpa only [d496, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1869 (p : Pattern) (guard : d4111 p = 1) : d497 p ≤ (0 : Int) + d515 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d497, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1861 p hg
    simpa only [d497, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d497, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1868 p hg
    simpa only [d497, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1870 (p : Pattern) (guard : d4111 p = 1) : d498 p ≤ (0 : Int) + d516 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d498, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1865 p hg
    simpa only [d498, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d498, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d498, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1871 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (0 : Int) + d208 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1872 (p : Pattern) (guard : d4058 p = 1) : d490 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d490, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d4058, d490, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d490, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1871 p hg
    simpa only [d4058, d490, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1873 (p : Pattern) (guard : d4058 p = 1) : d491 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d491, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1705 p hg
    simpa only [d491, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d491, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1872 p hg
    simpa only [d491, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1874 (p : Pattern) (guard : d0 p = 1) : d477 p ≤ (0 : Int) + d263 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1875 (p : Pattern) (guard : d4058 p = 1) : d495 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d495, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d4058, d495, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d495, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1874 p hg
    simpa only [d4058, d495, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1876 (p : Pattern) (guard : d4058 p = 1) : d496 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d496, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1705 p hg
    simpa only [d496, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d496, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1875 p hg
    simpa only [d496, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1877 (p : Pattern) (guard : d4058 p = 1) : d497 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d497, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1873 p hg
    simpa only [d497, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d497, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1876 p hg
    simpa only [d497, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1878 (p : Pattern) (guard : d4058 p = 1) : d498 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d498, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1712 p hg
    simpa only [d498, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d498, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1877 p hg
    simpa only [d498, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1879 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (2 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1880 (p : Pattern) (guard : d4058 p = 1) : d490 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d490, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1718 p hg
    simpa only [d4058, d490, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d490, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1879 p hg
    simpa only [d4058, d490, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1881 (p : Pattern) (guard : d4058 p = 1) : d491 p ≤ (2 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1720 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1880 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1882 (p : Pattern) (guard : d1 p = 1) : d164 p ≤ (2 : Int) + d164 p := by
  omega
theorem compare1883 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (2 : Int) + d166 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1884 (p : Pattern) (guard : d4058 p = 1) : d492 p ≤ (2 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d492, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1882 p hg
    simpa only [d4058, d492, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d492, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1883 p hg
    simpa only [d4058, d492, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1885 (p : Pattern) (guard : d4058 p = 1) : d493 p ≤ (2 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d493, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1720 p hg
    simpa only [d493, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d493, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1884 p hg
    simpa only [d493, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1886 (p : Pattern) (guard : d4058 p = 1) : d494 p ≤ (2 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d494, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1881 p hg
    simpa only [d494, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d494, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1885 p hg
    simpa only [d494, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1887 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (2 : Int) + d208 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1888 (p : Pattern) (guard : d4058 p = 1) : d490 p ≤ (2 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d490, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1718 p hg
    simpa only [d4058, d490, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d490, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1887 p hg
    simpa only [d4058, d490, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1889 (p : Pattern) (guard : d4058 p = 1) : d491 p ≤ (2 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d491, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1720 p hg
    simpa only [d491, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d491, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d491, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1890 (p : Pattern) (guard : d1 p = 1) : d225 p ≤ (2 : Int) + d225 p := by
  omega
theorem compare1891 (p : Pattern) (guard : d0 p = 1) : d477 p ≤ (2 : Int) + d263 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1892 (p : Pattern) (guard : d4058 p = 1) : d495 p ≤ (2 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d495, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1890 p hg
    simpa only [d4058, d495, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d495, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1891 p hg
    simpa only [d4058, d495, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1893 (p : Pattern) (guard : d4058 p = 1) : d496 p ≤ (2 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d496, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1720 p hg
    simpa only [d496, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d496, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1892 p hg
    simpa only [d496, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1894 (p : Pattern) (guard : d4058 p = 1) : d497 p ≤ (2 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d497, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1889 p hg
    simpa only [d497, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d497, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1893 p hg
    simpa only [d497, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1895 (p : Pattern) (guard : d4058 p = 1) : d498 p ≤ (2 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d498, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1886 p hg
    simpa only [d498, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d498, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1894 p hg
    simpa only [d498, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1896 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (0 : Int) + d77 p := by
  omega
theorem compare1897 (p : Pattern) (guard : d0 p = 1) : d87 p ≤ (0 : Int) + d400 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1898 (p : Pattern) (guard : d4068 p = 1) : d88 p ≤ (0 : Int) + d517 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d88, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d4068, d88, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d88, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1897 p hg
    simpa only [d4068, d88, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1899 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d544 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1900 (p : Pattern) (guard : d4113 p = 1) : d98 p ≤ (0 : Int) + d545 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d98, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1898 p hg
    simpa only [d4113, d98, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d98, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1899 p hg
    simpa only [d4113, d98, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1901 (p : Pattern) (guard : d0 p = 1) : d426 p ≤ (0 : Int) + d548 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1902 (p : Pattern) (guard : d4114 p = 1) : d489 p ≤ (0 : Int) + d549 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d489, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1900 p hg
    simpa only [d4114, d489, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d489, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1901 p hg
    simpa only [d4114, d489, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1903 (p : Pattern) (guard : d0 p = 1) : d87 p ≤ (0 : Int) + d439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1904 (p : Pattern) (guard : d4068 p = 1) : d88 p ≤ (0 : Int) + d550 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d88, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d4068, d88, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d88, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1903 p hg
    simpa only [d4068, d88, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1905 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d551 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1906 (p : Pattern) (guard : d4113 p = 1) : d98 p ≤ (0 : Int) + d552 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d98, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1904 p hg
    simpa only [d4113, d98, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d98, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1905 p hg
    simpa only [d4113, d98, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1907 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (0 : Int) + d554 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1908 (p : Pattern) (guard : d4114 p = 1) : d490 p ≤ (0 : Int) + d555 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d490, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1906 p hg
    simpa only [d4114, d490, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d490, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1907 p hg
    simpa only [d4114, d490, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1909 (p : Pattern) (guard : d4114 p = 1) : d491 p ≤ (0 : Int) + d556 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d491, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d491, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d491, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1908 p hg
    simpa only [d491, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1910 (p : Pattern) (guard : d1 p = 1) : d147 p ≤ (0 : Int) + d147 p := by
  omega
theorem compare1911 (p : Pattern) (guard : d0 p = 1) : d157 p ≤ (0 : Int) + d439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1912 (p : Pattern) (guard : d4068 p = 1) : d158 p ≤ (0 : Int) + d557 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d158, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1910 p hg
    simpa only [d4068, d158, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d158, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1911 p hg
    simpa only [d4068, d158, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1913 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d580 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1914 (p : Pattern) (guard : d4113 p = 1) : d164 p ≤ (0 : Int) + d581 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d164, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1912 p hg
    simpa only [d4113, d164, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d164, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1913 p hg
    simpa only [d4113, d164, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1915 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (0 : Int) + d584 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1916 (p : Pattern) (guard : d4114 p = 1) : d492 p ≤ (0 : Int) + d585 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d492, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1914 p hg
    simpa only [d4114, d492, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d492, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1915 p hg
    simpa only [d4114, d492, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1917 (p : Pattern) (guard : d4114 p = 1) : d493 p ≤ (0 : Int) + d586 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d493, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d493, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d493, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1916 p hg
    simpa only [d493, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1918 (p : Pattern) (guard : d4114 p = 1) : d494 p ≤ (0 : Int) + d587 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d494, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1909 p hg
    simpa only [d494, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d494, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1917 p hg
    simpa only [d494, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1919 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (0 : Int) + d607 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1920 (p : Pattern) (guard : d4114 p = 1) : d490 p ≤ (0 : Int) + d608 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d490, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1906 p hg
    simpa only [d4114, d490, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d490, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1919 p hg
    simpa only [d4114, d490, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1921 (p : Pattern) (guard : d4114 p = 1) : d491 p ≤ (0 : Int) + d609 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d491, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d491, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d491, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1920 p hg
    simpa only [d491, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1922 (p : Pattern) (guard : d1 p = 1) : d220 p ≤ (0 : Int) + d220 p := by
  omega
theorem compare1923 (p : Pattern) (guard : d0 p = 1) : d222 p ≤ (0 : Int) + d457 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1924 (p : Pattern) (guard : d4068 p = 1) : d223 p ≤ (0 : Int) + d610 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d223, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d4068, d223, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d223, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1923 p hg
    simpa only [d4068, d223, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1925 (p : Pattern) (guard : d0 p = 1) : d224 p ≤ (0 : Int) + d617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1926 (p : Pattern) (guard : d4113 p = 1) : d225 p ≤ (0 : Int) + d618 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d225, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1924 p hg
    simpa only [d4113, d225, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d225, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1925 p hg
    simpa only [d4113, d225, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1927 (p : Pattern) (guard : d0 p = 1) : d477 p ≤ (0 : Int) + d648 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1928 (p : Pattern) (guard : d4114 p = 1) : d495 p ≤ (0 : Int) + d649 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d495, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1926 p hg
    simpa only [d4114, d495, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d495, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1927 p hg
    simpa only [d4114, d495, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1929 (p : Pattern) (guard : d4114 p = 1) : d496 p ≤ (0 : Int) + d650 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d496, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d496, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d496, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1928 p hg
    simpa only [d496, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1930 (p : Pattern) (guard : d4114 p = 1) : d497 p ≤ (0 : Int) + d651 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d497, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1921 p hg
    simpa only [d497, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d497, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1929 p hg
    simpa only [d497, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1931 (p : Pattern) (guard : d4114 p = 1) : d498 p ≤ (0 : Int) + d652 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d498, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1918 p hg
    simpa only [d498, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d498, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1930 p hg
    simpa only [d498, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1932 (p : Pattern) (guard : d0 p = 1) : d413 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1933 (p : Pattern) (guard : d4066 p = 1) : d499 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d499, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d4066, d499, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d499, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1932 p hg
    simpa only [d4066, d499, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1934 (p : Pattern) (guard : d0 p = 1) : d425 p ≤ (0 : Int) + d99 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1935 (p : Pattern) (guard : d4066 p = 1) : d500 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d500, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d4066, d500, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d500, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d4066, d500, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1936 (p : Pattern) (guard : d4066 p = 1) : d501 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d501, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1933 p hg
    simpa only [d501, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d501, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1935 p hg
    simpa only [d501, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1937 (p : Pattern) (guard : d0 p = 1) : d442 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1938 (p : Pattern) (guard : d4066 p = 1) : d502 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d502, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d4066, d502, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d502, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1937 p hg
    simpa only [d4066, d502, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1939 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d99 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1940 (p : Pattern) (guard : d4066 p = 1) : d503 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d503, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d4066, d503, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d503, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1939 p hg
    simpa only [d4066, d503, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1941 (p : Pattern) (guard : d4066 p = 1) : d504 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d504, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1938 p hg
    simpa only [d504, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d504, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1940 p hg
    simpa only [d504, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1942 (p : Pattern) (guard : d4066 p = 1) : d505 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1936 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1941 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1943 (p : Pattern) (guard : d0 p = 1) : d442 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1944 (p : Pattern) (guard : d4066 p = 1) : d506 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d506, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d4066, d506, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d506, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1943 p hg
    simpa only [d4066, d506, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1945 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1946 (p : Pattern) (guard : d4066 p = 1) : d507 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d507, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d4066, d507, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d507, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1945 p hg
    simpa only [d4066, d507, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1947 (p : Pattern) (guard : d4066 p = 1) : d508 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d508, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1944 p hg
    simpa only [d508, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d508, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1946 p hg
    simpa only [d508, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1948 (p : Pattern) (guard : d4066 p = 1) : d509 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d509, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1936 p hg
    simpa only [d509, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d509, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1947 p hg
    simpa only [d509, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1949 (p : Pattern) (guard : d4066 p = 1) : d510 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d510, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1942 p hg
    simpa only [d510, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d510, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1948 p hg
    simpa only [d510, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1950 (p : Pattern) (guard : d0 p = 1) : d463 p ≤ (0 : Int) + d224 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1951 (p : Pattern) (guard : d4066 p = 1) : d511 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d511, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1138 p hg
    simpa only [d4066, d511, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d511, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1950 p hg
    simpa only [d4066, d511, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1952 (p : Pattern) (guard : d0 p = 1) : d476 p ≤ (0 : Int) + d307 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1953 (p : Pattern) (guard : d4066 p = 1) : d512 p ≤ (0 : Int) + d308 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d512, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1141 p hg
    simpa only [d4066, d512, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d512, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1952 p hg
    simpa only [d4066, d512, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1954 (p : Pattern) (guard : d4066 p = 1) : d513 p ≤ (0 : Int) + d309 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d513, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1951 p hg
    simpa only [d513, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d513, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1953 p hg
    simpa only [d513, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1955 (p : Pattern) (guard : d4066 p = 1) : d514 p ≤ (0 : Int) + d310 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d514, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1936 p hg
    simpa only [d514, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d514, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1954 p hg
    simpa only [d514, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1956 (p : Pattern) (guard : d4066 p = 1) : d515 p ≤ (0 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d515, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1942 p hg
    simpa only [d515, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d515, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1955 p hg
    simpa only [d515, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1957 (p : Pattern) (guard : d4066 p = 1) : d516 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d516, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1949 p hg
    simpa only [d516, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d516, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1956 p hg
    simpa only [d516, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1958 (p : Pattern) (guard : d0 p = 1) : d413 p ≤ (0 : Int) + d544 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1959 (p : Pattern) (guard : d4113 p = 1) : d499 p ≤ (0 : Int) + d545 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d499, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1898 p hg
    simpa only [d4113, d499, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d499, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1958 p hg
    simpa only [d4113, d499, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
