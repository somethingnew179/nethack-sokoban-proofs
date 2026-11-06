/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1820 (p : Pattern) (guard : d1088 p = 1) : d14 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1580 p hg
    simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1821 (p : Pattern) (guard : d1088 p = 1) : d98 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1820 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1822 (p : Pattern) (guard : d1088 p = 1) : d98 p ≤ (0 : Int) + d502 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1819 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1821 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1823 (p : Pattern) (guard : d1088 p = 1) : d99 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1821 p hg
    simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1637 p hg
    simpa only [d99, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1824 (p : Pattern) (guard : d1088 p = 1) : d100 p ≤ (0 : Int) + d503 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d100, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d100, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d100, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d100, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1825 (p : Pattern) (guard : d1088 p = 1) : d99 p ≤ (0 : Int) + d504 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d99, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1819 p hg
    simpa only [d99, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d99, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1637 p hg
    simpa only [d99, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1826 (p : Pattern) (guard : d1088 p = 1) : d40 p ≤ (0 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1604 p hg
    simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1827 (p : Pattern) (guard : d1088 p = 1) : d69 p ≤ (0 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1828 (p : Pattern) (guard : d1088 p = 1) : d72 p ≤ (0 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1827 p hg
    simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1637 p hg
    simpa only [d72, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1829 (p : Pattern) (guard : d1088 p = 1) : d101 p ≤ (0 : Int) + d505 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d101, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1825 p hg
    simpa only [d101, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d101, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1828 p hg
    simpa only [d101, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1830 (p : Pattern) (guard : d1088 p = 1) : d102 p ≤ (0 : Int) + d506 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d102, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d102, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d102, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d102, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1831 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1832 (p : Pattern) (guard : d1095 p = 1) : d236 p ≤ (0 : Int) + d508 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d236, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d1095, d236, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d236, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1831 p hg
    simpa only [d1095, d236, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1833 (p : Pattern) (guard : d1095 p = 1) : d237 p ≤ (0 : Int) + d509 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d237, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1815 p hg
    simpa only [d237, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d237, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1832 p hg
    simpa only [d237, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1834 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1835 (p : Pattern) (guard : d1095 p = 1) : d238 p ≤ (0 : Int) + d513 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d238, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d1095, d238, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d238, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1834 p hg
    simpa only [d1095, d238, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1836 (p : Pattern) (guard : d1088 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare1837 (p : Pattern) (guard : d1088 p = 1) : d107 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1836 p hg
    simpa only [d107, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1838 (p : Pattern) (guard : d1088 p = 1) : d108 p ≤ (0 : Int) + d514 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d108, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d108, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d108, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1837 p hg
    simpa only [d108, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1839 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1840 (p : Pattern) (guard : d1095 p = 1) : d239 p ≤ (0 : Int) + d515 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d239, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1838 p hg
    simpa only [d1095, d239, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d239, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1839 p hg
    simpa only [d1095, d239, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1841 (p : Pattern) (guard : d1095 p = 1) : d240 p ≤ (0 : Int) + d516 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d240, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1835 p hg
    simpa only [d240, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d240, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1840 p hg
    simpa only [d240, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1842 (p : Pattern) (guard : d1095 p = 1) : d241 p ≤ (0 : Int) + d517 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d241, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1833 p hg
    simpa only [d241, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d241, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1841 p hg
    simpa only [d241, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1843 (p : Pattern) (guard : d1095 p = 1) : d242 p ≤ (0 : Int) + d518 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d242, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1813 p hg
    simpa only [d242, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d242, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1842 p hg
    simpa only [d242, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1844 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d521 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1845 (p : Pattern) (guard : d1095 p = 1) : d243 p ≤ (0 : Int) + d522 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d243, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d1095, d243, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d243, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1844 p hg
    simpa only [d1095, d243, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1846 (p : Pattern) (guard : d1095 p = 1) : d244 p ≤ (0 : Int) + d523 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d244, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1815 p hg
    simpa only [d244, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d244, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1845 p hg
    simpa only [d244, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1847 (p : Pattern) (guard : d1088 p = 1) : d79 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d79, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1797 p hg
    simpa only [d79, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d79, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d79, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1848 (p : Pattern) (guard : d1088 p = 1) : d80 p ≤ (0 : Int) + d492 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d80, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1798 p hg
    simpa only [d80, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d80, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1847 p hg
    simpa only [d80, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1849 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d525 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1850 (p : Pattern) (guard : d1095 p = 1) : d245 p ≤ (0 : Int) + d526 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d245, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1848 p hg
    simpa only [d1095, d245, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d245, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1849 p hg
    simpa only [d1095, d245, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1851 (p : Pattern) (guard : d1095 p = 1) : d246 p ≤ (0 : Int) + d527 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d246, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1835 p hg
    simpa only [d246, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d246, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1850 p hg
    simpa only [d246, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1852 (p : Pattern) (guard : d1095 p = 1) : d247 p ≤ (0 : Int) + d528 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d247, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1846 p hg
    simpa only [d247, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d247, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1851 p hg
    simpa only [d247, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1853 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d529 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1854 (p : Pattern) (guard : d1095 p = 1) : d248 p ≤ (0 : Int) + d530 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d248, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1716 p hg
    simpa only [d1095, d248, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d248, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1853 p hg
    simpa only [d1095, d248, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1855 (p : Pattern) (guard : d1088 p = 1) : d101 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1828 p hg
    simpa only [d101, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1856 (p : Pattern) (guard : d1088 p = 1) : d102 p ≤ (0 : Int) + d507 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d102, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d102, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d102, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1855 p hg
    simpa only [d102, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1857 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1858 (p : Pattern) (guard : d1095 p = 1) : d249 p ≤ (0 : Int) + d531 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d249, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1856 p hg
    simpa only [d1095, d249, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d249, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1857 p hg
    simpa only [d1095, d249, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1859 (p : Pattern) (guard : d1095 p = 1) : d250 p ≤ (0 : Int) + d532 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d250, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1854 p hg
    simpa only [d250, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d250, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1858 p hg
    simpa only [d250, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1860 (p : Pattern) (guard : d0 p = 1) : d167 p ≤ (0 : Int) + d525 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1861 (p : Pattern) (guard : d1095 p = 1) : d251 p ≤ (0 : Int) + d533 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d251, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d1095, d251, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d251, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1860 p hg
    simpa only [d1095, d251, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1862 (p : Pattern) (guard : d1095 p = 1) : d130 p ≤ (0 : Int) + d130 p := by
  omega
theorem compare1863 (p : Pattern) (guard : d1095 p = 1) : d252 p ≤ (0 : Int) + d534 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d252, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1861 p hg
    simpa only [d252, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d252, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1862 p hg
    simpa only [d252, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1864 (p : Pattern) (guard : d1095 p = 1) : d253 p ≤ (0 : Int) + d535 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d253, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1859 p hg
    simpa only [d253, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d253, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1863 p hg
    simpa only [d253, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1865 (p : Pattern) (guard : d1095 p = 1) : d254 p ≤ (0 : Int) + d536 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d254, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1852 p hg
    simpa only [d254, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d254, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1864 p hg
    simpa only [d254, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1866 (p : Pattern) (guard : d1095 p = 1) : d255 p ≤ (0 : Int) + d537 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d255, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1843 p hg
    simpa only [d255, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d255, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1865 p hg
    simpa only [d255, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1867 (p : Pattern) (guard : d1087 p = 1) : d8 p ≤ (1 : Int) + d8 p := by
  omega
theorem compare1868 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (1 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1869 (p : Pattern) (guard : d1087 p = 1) : d15 p ≤ (1 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1868 p hg
    simpa only [d1087, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1371 p hg
    simpa only [d1087, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1870 (p : Pattern) (guard : d1087 p = 1) : d16 p ≤ (1 : Int) + d8 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1867 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1871 (p : Pattern) (guard : d1087 p = 1) : d20 p ≤ (1 : Int) + d20 p := by
  omega
theorem compare1872 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (1 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1873 (p : Pattern) (guard : d1087 p = 1) : d25 p ≤ (1 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1872 p hg
    simpa only [d1087, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1377 p hg
    simpa only [d1087, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1874 (p : Pattern) (guard : d1087 p = 1) : d26 p ≤ (1 : Int) + d20 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1871 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1873 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1875 (p : Pattern) (guard : d1087 p = 1) : d27 p ≤ (1 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d27, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1870 p hg
    simpa only [d27, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d27, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1874 p hg
    simpa only [d27, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1876 (p : Pattern) (guard : d1087 p = 1) : d28 p ≤ (1 : Int) + d1098 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d28, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1870 p hg
    simpa only [d28, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d28, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1875 p hg
    simpa only [d28, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1877 (p : Pattern) (guard : d1087 p = 1) : d33 p ≤ (1 : Int) + d33 p := by
  omega
theorem compare1878 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (1 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1879 (p : Pattern) (guard : d1087 p = 1) : d34 p ≤ (1 : Int) + d33 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1878 p hg
    simpa only [d1087, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1386 p hg
    simpa only [d1087, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1880 (p : Pattern) (guard : d1087 p = 1) : d35 p ≤ (1 : Int) + d33 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1877 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1879 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1881 (p : Pattern) (guard : d1087 p = 1) : d36 p ≤ (1 : Int) + d1099 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d36, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1870 p hg
    simpa only [d36, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d36, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1880 p hg
    simpa only [d36, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1882 (p : Pattern) (guard : d1087 p = 1) : d38 p ≤ (1 : Int) + d38 p := by
  omega
theorem compare1883 (p : Pattern) (guard : d0 p = 1) : d38 p ≤ (1 : Int) + d38 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1884 (p : Pattern) (guard : d1087 p = 1) : d41 p ≤ (1 : Int) + d38 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1883 p hg
    simpa only [d1087, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1392 p hg
    simpa only [d1087, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1885 (p : Pattern) (guard : d1087 p = 1) : d42 p ≤ (1 : Int) + d38 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1882 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1884 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1886 (p : Pattern) (guard : d1087 p = 1) : d43 p ≤ (1 : Int) + d1100 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d43, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1885 p hg
    simpa only [d43, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d43, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1874 p hg
    simpa only [d43, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1887 (p : Pattern) (guard : d1087 p = 1) : d44 p ≤ (1 : Int) + d1101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d44, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1881 p hg
    simpa only [d44, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d44, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1886 p hg
    simpa only [d44, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1888 (p : Pattern) (guard : d1087 p = 1) : d45 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d45, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1876 p hg
    simpa only [d45, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d45, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1887 p hg
    simpa only [d45, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1889 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1890 (p : Pattern) (guard : d1096 p = 1) : d228 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d1096, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1889 p hg
    simpa only [d1096, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1891 (p : Pattern) (guard : d1087 p = 1) : d46 p ≤ (1 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d46, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d46, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d46, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1873 p hg
    simpa only [d46, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1892 (p : Pattern) (guard : d1087 p = 1) : d47 p ≤ (1 : Int) + d1098 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d47, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d47, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d47, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1891 p hg
    simpa only [d47, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1893 (p : Pattern) (guard : d1087 p = 1) : d48 p ≤ (1 : Int) + d1099 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d48, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d48, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d48, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1879 p hg
    simpa only [d48, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1894 (p : Pattern) (guard : d1087 p = 1) : d49 p ≤ (1 : Int) + d1100 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d49, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1884 p hg
    simpa only [d49, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d49, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1873 p hg
    simpa only [d49, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1895 (p : Pattern) (guard : d1087 p = 1) : d50 p ≤ (1 : Int) + d1101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d50, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1893 p hg
    simpa only [d50, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d50, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1894 p hg
    simpa only [d50, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1896 (p : Pattern) (guard : d1087 p = 1) : d51 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d51, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1892 p hg
    simpa only [d51, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d51, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1895 p hg
    simpa only [d51, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1897 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1898 (p : Pattern) (guard : d1096 p = 1) : d229 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d1096, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1897 p hg
    simpa only [d1096, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1899 (p : Pattern) (guard : d1096 p = 1) : d230 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1890 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1898 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1900 (p : Pattern) (guard : d1087 p = 1) : d40 p ≤ (1 : Int) + d40 p := by
  omega
theorem compare1901 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (1 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1902 (p : Pattern) (guard : d1087 p = 1) : d68 p ≤ (1 : Int) + d40 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1901 p hg
    simpa only [d1087, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d1087, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1903 (p : Pattern) (guard : d1087 p = 1) : d69 p ≤ (1 : Int) + d40 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1900 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1904 (p : Pattern) (guard : d1087 p = 1) : d24 p ≤ (1 : Int) + d24 p := by
  omega
theorem compare1905 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (1 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1906 (p : Pattern) (guard : d1087 p = 1) : d70 p ≤ (1 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1905 p hg
    simpa only [d1087, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d1087, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1907 (p : Pattern) (guard : d1087 p = 1) : d71 p ≤ (1 : Int) + d24 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1904 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1906 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1908 (p : Pattern) (guard : d1087 p = 1) : d72 p ≤ (1 : Int) + d1103 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d72, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1903 p hg
    simpa only [d72, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d72, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1907 p hg
    simpa only [d72, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1909 (p : Pattern) (guard : d1087 p = 1) : d73 p ≤ (1 : Int) + d1104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d73, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1875 p hg
    simpa only [d73, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d73, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1908 p hg
    simpa only [d73, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1910 (p : Pattern) (guard : d1087 p = 1) : d74 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d74, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1876 p hg
    simpa only [d74, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d74, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1909 p hg
    simpa only [d74, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1911 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (1 : Int) + d1105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1912 (p : Pattern) (guard : d1096 p = 1) : d231 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1910 p hg
    simpa only [d1096, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1911 p hg
    simpa only [d1096, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1913 (p : Pattern) (guard : d1087 p = 1) : d75 p ≤ (1 : Int) + d1103 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d75, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d75, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d75, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1906 p hg
    simpa only [d75, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1914 (p : Pattern) (guard : d1087 p = 1) : d79 p ≤ (1 : Int) + d1104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d79, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1891 p hg
    simpa only [d79, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d79, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1913 p hg
    simpa only [d79, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1915 (p : Pattern) (guard : d1087 p = 1) : d80 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d80, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1892 p hg
    simpa only [d80, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d80, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1914 p hg
    simpa only [d80, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1916 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (1 : Int) + d1105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1917 (p : Pattern) (guard : d1096 p = 1) : d232 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1915 p hg
    simpa only [d1096, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1916 p hg
    simpa only [d1096, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1918 (p : Pattern) (guard : d1096 p = 1) : d233 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1912 p hg
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1917 p hg
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1919 (p : Pattern) (guard : d1096 p = 1) : d234 p ≤ (1 : Int) + d1106 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d234, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1899 p hg
    simpa only [d234, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d234, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1918 p hg
    simpa only [d234, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1920 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1921 (p : Pattern) (guard : d1096 p = 1) : d235 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d1096, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1920 p hg
    simpa only [d1096, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1922 (p : Pattern) (guard : d1087 p = 1) : d14 p ≤ (1 : Int) + d14 p := by
  omega
theorem compare1923 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (1 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1924 (p : Pattern) (guard : d1087 p = 1) : d97 p ≤ (1 : Int) + d14 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1923 p hg
    simpa only [d1087, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare387 p hg
    simpa only [d1087, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1925 (p : Pattern) (guard : d1087 p = 1) : d98 p ≤ (1 : Int) + d14 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1924 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1926 (p : Pattern) (guard : d1087 p = 1) : d99 p ≤ (1 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d99, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1925 p hg
    simpa only [d99, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d99, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1907 p hg
    simpa only [d99, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1927 (p : Pattern) (guard : d1087 p = 1) : d100 p ≤ (1 : Int) + d1108 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d100, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1925 p hg
    simpa only [d100, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d100, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1926 p hg
    simpa only [d100, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1928 (p : Pattern) (guard : d1087 p = 1) : d101 p ≤ (1 : Int) + d1109 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d101, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1926 p hg
    simpa only [d101, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d101, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1908 p hg
    simpa only [d101, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1929 (p : Pattern) (guard : d1087 p = 1) : d102 p ≤ (1 : Int) + d1110 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d102, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1927 p hg
    simpa only [d102, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d102, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1928 p hg
    simpa only [d102, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1930 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (1 : Int) + d1110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1931 (p : Pattern) (guard : d1096 p = 1) : d236 p ≤ (1 : Int) + d1110 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1929 p hg
    simpa only [d1096, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1930 p hg
    simpa only [d1096, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1932 (p : Pattern) (guard : d1096 p = 1) : d237 p ≤ (1 : Int) + d1111 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d237, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1921 p hg
    simpa only [d237, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d237, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1931 p hg
    simpa only [d237, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1933 (p : Pattern) (guard : d1087 p = 1) : d76 p ≤ (1 : Int) + d1104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d76, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1875 p hg
    simpa only [d76, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d76, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1913 p hg
    simpa only [d76, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1934 (p : Pattern) (guard : d1087 p = 1) : d77 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d77, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1876 p hg
    simpa only [d77, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d77, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1933 p hg
    simpa only [d77, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1935 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (1 : Int) + d1105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1936 (p : Pattern) (guard : d1096 p = 1) : d238 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d1096, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1935 p hg
    simpa only [d1096, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1937 (p : Pattern) (guard : d1087 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare1938 (p : Pattern) (guard : d1087 p = 1) : d107 p ≤ (1 : Int) + d1112 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d107, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1926 p hg
    simpa only [d107, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d107, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1937 p hg
    simpa only [d107, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1939 (p : Pattern) (guard : d1087 p = 1) : d108 p ≤ (1 : Int) + d1113 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d108, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1927 p hg
    simpa only [d108, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d108, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1938 p hg
    simpa only [d108, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1940 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (1 : Int) + d1113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1941 (p : Pattern) (guard : d1096 p = 1) : d239 p ≤ (1 : Int) + d1113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1939 p hg
    simpa only [d1096, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1940 p hg
    simpa only [d1096, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1942 (p : Pattern) (guard : d1096 p = 1) : d240 p ≤ (1 : Int) + d1114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d240, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1936 p hg
    simpa only [d240, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d240, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1941 p hg
    simpa only [d240, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1943 (p : Pattern) (guard : d1096 p = 1) : d241 p ≤ (1 : Int) + d1115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d241, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1932 p hg
    simpa only [d241, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d241, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1942 p hg
    simpa only [d241, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1944 (p : Pattern) (guard : d1096 p = 1) : d242 p ≤ (1 : Int) + d1116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d242, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1919 p hg
    simpa only [d242, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d242, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1943 p hg
    simpa only [d242, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1945 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1946 (p : Pattern) (guard : d1096 p = 1) : d243 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d1096, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1945 p hg
    simpa only [d1096, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1947 (p : Pattern) (guard : d1096 p = 1) : d244 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1921 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1946 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1948 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (1 : Int) + d1105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1949 (p : Pattern) (guard : d1096 p = 1) : d245 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1915 p hg
    simpa only [d1096, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1948 p hg
    simpa only [d1096, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1950 (p : Pattern) (guard : d1096 p = 1) : d246 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1936 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1949 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1951 (p : Pattern) (guard : d1096 p = 1) : d247 p ≤ (1 : Int) + d1106 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d247, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1947 p hg
    simpa only [d247, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d247, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1950 p hg
    simpa only [d247, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1952 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1953 (p : Pattern) (guard : d1096 p = 1) : d248 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d1096, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1952 p hg
    simpa only [d1096, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1954 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (1 : Int) + d1110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1955 (p : Pattern) (guard : d1096 p = 1) : d249 p ≤ (1 : Int) + d1110 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1929 p hg
    simpa only [d1096, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1954 p hg
    simpa only [d1096, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1956 (p : Pattern) (guard : d1096 p = 1) : d250 p ≤ (1 : Int) + d1111 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d250, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1953 p hg
    simpa only [d250, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d250, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1955 p hg
    simpa only [d250, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1957 (p : Pattern) (guard : d0 p = 1) : d167 p ≤ (1 : Int) + d1105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1958 (p : Pattern) (guard : d1096 p = 1) : d251 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d1096, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1957 p hg
    simpa only [d1096, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1959 (p : Pattern) (guard : d1087 p = 1) : d109 p ≤ (1 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d109, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1924 p hg
    simpa only [d109, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d109, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1906 p hg
    simpa only [d109, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
