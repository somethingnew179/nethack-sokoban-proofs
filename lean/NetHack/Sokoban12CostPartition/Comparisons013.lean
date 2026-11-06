/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1820 (p : Pattern) (guard : d794 p = 1) : d340 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1817 p hg
    simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1819 p hg
    simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1821 (p : Pattern) (guard : d794 p = 1) : d211 p ≤ (2 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1807 p hg
    simpa only [d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1822 (p : Pattern) (guard : d794 p = 1) : d212 p ≤ (2 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1812 p hg
    simpa only [d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1823 (p : Pattern) (guard : d794 p = 1) : d213 p ≤ (2 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1821 p hg
    simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1824 (p : Pattern) (guard : d794 p = 1) : d341 p ≤ (2 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1820 p hg
    simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1825 (p : Pattern) (guard : d794 p = 1) : d342 p ≤ (2 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d342, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1815 p hg
    simpa only [d342, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d342, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d342, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1826 (p : Pattern) (guard : d794 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare1827 (p : Pattern) (guard : d794 p = 1) : d343 p ≤ (2 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1828 (p : Pattern) (guard : d794 p = 1) : d344 p ≤ (2 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d344, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1825 p hg
    simpa only [d344, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d344, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1827 p hg
    simpa only [d344, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1829 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1830 (p : Pattern) (guard : d794 p = 1) : d114 p ≤ (2 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d114, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d794, d114, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d114, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d794, d114, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1831 (p : Pattern) (guard : d794 p = 1) : d114 p ≤ (2 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1801 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1832 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1833 (p : Pattern) (guard : d794 p = 1) : d116 p ≤ (2 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d116, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d794, d116, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d116, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1832 p hg
    simpa only [d794, d116, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1834 (p : Pattern) (guard : d794 p = 1) : d116 p ≤ (2 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1833 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1835 (p : Pattern) (guard : d794 p = 1) : d335 p ≤ (2 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d335, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1831 p hg
    simpa only [d335, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d335, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1834 p hg
    simpa only [d335, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1836 (p : Pattern) (guard : d794 p = 1) : d345 p ≤ (2 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d345, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1835 p hg
    simpa only [d345, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d345, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d345, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1837 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (2 : Int) + d138 p := by
  omega
theorem compare1838 (p : Pattern) (guard : d794 p = 1) : d346 p ≤ (2 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d346, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1837 p hg
    simpa only [d794, d346, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d346, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d794, d346, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1839 (p : Pattern) (guard : d794 p = 1) : d347 p ≤ (2 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1838 p hg
    simpa only [d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1840 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (2 : Int) + d145 p := by
  omega
theorem compare1841 (p : Pattern) (guard : d794 p = 1) : d348 p ≤ (2 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d348, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1840 p hg
    simpa only [d794, d348, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d348, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1832 p hg
    simpa only [d794, d348, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1842 (p : Pattern) (guard : d794 p = 1) : d349 p ≤ (2 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1841 p hg
    simpa only [d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1843 (p : Pattern) (guard : d794 p = 1) : d350 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1839 p hg
    simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1842 p hg
    simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1844 (p : Pattern) (guard : d794 p = 1) : d351 p ≤ (2 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1843 p hg
    simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1845 (p : Pattern) (guard : d794 p = 1) : d352 p ≤ (2 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d352, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1836 p hg
    simpa only [d352, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d352, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1844 p hg
    simpa only [d352, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1846 (p : Pattern) (guard : d794 p = 1) : d338 p ≤ (2 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1847 (p : Pattern) (guard : d794 p = 1) : d339 p ≤ (2 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1833 p hg
    simpa only [d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1848 (p : Pattern) (guard : d794 p = 1) : d340 p ≤ (2 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1846 p hg
    simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1847 p hg
    simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1849 (p : Pattern) (guard : d794 p = 1) : d353 p ≤ (2 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1848 p hg
    simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1850 (p : Pattern) (guard : d794 p = 1) : d354 p ≤ (2 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1849 p hg
    simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1851 (p : Pattern) (guard : d794 p = 1) : d355 p ≤ (2 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d355, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1845 p hg
    simpa only [d355, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d355, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1850 p hg
    simpa only [d355, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1852 (p : Pattern) (guard : d794 p = 1) : d356 p ≤ (2 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d356, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1828 p hg
    simpa only [d356, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d356, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1851 p hg
    simpa only [d356, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1853 (p : Pattern) (guard : d818 p = 1) : d114 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1854 (p : Pattern) (guard : d818 p = 1) : d116 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare696 p hg
    simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1855 (p : Pattern) (guard : d818 p = 1) : d335 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d335, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1853 p hg
    simpa only [d335, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d335, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1854 p hg
    simpa only [d335, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1856 (p : Pattern) (guard : d818 p = 1) : d336 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d336, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d336, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d336, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d336, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1857 (p : Pattern) (guard : d818 p = 1) : d337 p ≤ (0 : Int) + d227 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1855 p hg
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1856 p hg
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1858 (p : Pattern) (guard : d818 p = 1) : d338 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d338, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1853 p hg
    simpa only [d338, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d338, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d338, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1859 (p : Pattern) (guard : d818 p = 1) : d339 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d339, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1854 p hg
    simpa only [d339, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d339, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d339, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1860 (p : Pattern) (guard : d818 p = 1) : d340 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d340, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1858 p hg
    simpa only [d340, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d340, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1859 p hg
    simpa only [d340, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1861 (p : Pattern) (guard : d818 p = 1) : d341 p ≤ (0 : Int) + d231 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1860 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1862 (p : Pattern) (guard : d818 p = 1) : d342 p ≤ (0 : Int) + d366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d342, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1857 p hg
    simpa only [d342, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d342, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1861 p hg
    simpa only [d342, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1863 (p : Pattern) (guard : d818 p = 1) : d343 p ≤ (0 : Int) + d367 p := by
  cases selected : p 133 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d343, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1861 p hg
    simpa only [d343, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d343, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d343, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1864 (p : Pattern) (guard : d818 p = 1) : d344 p ≤ (0 : Int) + d368 p := by
  cases selected : p 132 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d344, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1862 p hg
    simpa only [d344, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d344, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1863 p hg
    simpa only [d344, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1865 (p : Pattern) (guard : d818 p = 1) : d345 p ≤ (0 : Int) + d369 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d345, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1855 p hg
    simpa only [d345, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d345, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d345, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1866 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1867 (p : Pattern) (guard : d758 p = 1) : d138 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d758, d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1866 p hg
    simpa only [d758, d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1868 (p : Pattern) (guard : d818 p = 1) : d346 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1867 p hg
    simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1869 (p : Pattern) (guard : d818 p = 1) : d347 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d347, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1868 p hg
    simpa only [d347, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d347, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d347, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1870 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1871 (p : Pattern) (guard : d758 p = 1) : d145 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d758, d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1870 p hg
    simpa only [d758, d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1872 (p : Pattern) (guard : d818 p = 1) : d348 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1871 p hg
    simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare696 p hg
    simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1873 (p : Pattern) (guard : d818 p = 1) : d349 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d349, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1872 p hg
    simpa only [d349, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d349, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d349, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1874 (p : Pattern) (guard : d818 p = 1) : d350 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d350, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d350, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d350, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1873 p hg
    simpa only [d350, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1875 (p : Pattern) (guard : d818 p = 1) : d351 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d351, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1874 p hg
    simpa only [d351, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d351, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d351, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1876 (p : Pattern) (guard : d818 p = 1) : d352 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d352, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1865 p hg
    simpa only [d352, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d352, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1875 p hg
    simpa only [d352, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1877 (p : Pattern) (guard : d818 p = 1) : d353 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d353, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1860 p hg
    simpa only [d353, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d353, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d353, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1878 (p : Pattern) (guard : d818 p = 1) : d354 p ≤ (0 : Int) + d372 p := by
  cases selected : p 133 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d354, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1877 p hg
    simpa only [d354, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d354, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d354, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1879 (p : Pattern) (guard : d818 p = 1) : d355 p ≤ (0 : Int) + d373 p := by
  cases selected : p 132 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d355, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1876 p hg
    simpa only [d355, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d355, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1878 p hg
    simpa only [d355, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1880 (p : Pattern) (guard : d818 p = 1) : d356 p ≤ (0 : Int) + d374 p := by
  cases selected : p 108 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d356, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1864 p hg
    simpa only [d356, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d356, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1879 p hg
    simpa only [d356, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1881 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (6 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1882 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (6 : Int) + d7 p := by
  omega
theorem compare1883 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (6 : Int) + d0 p := by
  change (2 : Int) ≤ (6 : Int) + 0
  decide
theorem compare1884 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (6 : Int) + d2 p := by
  change (4 : Int) ≤ (6 : Int) + 2
  decide
theorem compare1885 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (6 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1883 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1884 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1886 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (6 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1883 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1885 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1887 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (6 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1882 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1886 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1888 (p : Pattern) (guard : d757 p = 1) : d57 p ≤ (6 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1881 p hg
    simpa only [d757, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1887 p hg
    simpa only [d757, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1889 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (6 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1890 (p : Pattern) (guard : d1014 p = 1) : d114 p ≤ (6 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d1014, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1889 p hg
    simpa only [d1014, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1891 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (6 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1892 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (6 : Int) + d11 p := by
  omega
theorem compare1893 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (6 : Int) + d1 p := by
  change (3 : Int) ≤ (6 : Int) + 1
  decide
theorem compare1894 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (6 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1883 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1893 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1895 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (6 : Int) + d3 p := by
  change (5 : Int) ≤ (6 : Int) + 3
  decide
theorem compare1896 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (6 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1884 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1895 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1897 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (6 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1894 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1898 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (6 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1894 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1897 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1899 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (6 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1892 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1898 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1900 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (6 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1887 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1899 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1901 (p : Pattern) (guard : d757 p = 1) : d63 p ≤ (6 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1891 p hg
    simpa only [d757, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1900 p hg
    simpa only [d757, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1902 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (6 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1903 (p : Pattern) (guard : d1014 p = 1) : d116 p ≤ (6 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1901 p hg
    simpa only [d1014, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d1014, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1904 (p : Pattern) (guard : d1014 p = 1) : d335 p ≤ (6 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d335, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1890 p hg
    simpa only [d335, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d335, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1903 p hg
    simpa only [d335, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1905 (p : Pattern) (guard : d757 p = 1) : d106 p ≤ (6 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1881 p hg
    simpa only [d757, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1886 p hg
    simpa only [d757, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1906 (p : Pattern) (guard : d1014 p = 1) : d107 p ≤ (6 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1905 p hg
    simpa only [d1014, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1889 p hg
    simpa only [d1014, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1907 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (6 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1886 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1898 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1908 (p : Pattern) (guard : d757 p = 1) : d109 p ≤ (6 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1891 p hg
    simpa only [d757, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1907 p hg
    simpa only [d757, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1909 (p : Pattern) (guard : d1014 p = 1) : d110 p ≤ (6 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1908 p hg
    simpa only [d1014, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d1014, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1910 (p : Pattern) (guard : d1014 p = 1) : d336 p ≤ (6 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d336, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1906 p hg
    simpa only [d336, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d336, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1909 p hg
    simpa only [d336, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1911 (p : Pattern) (guard : d1014 p = 1) : d337 p ≤ (6 : Int) + d13 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1904 p hg
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1910 p hg
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1912 (p : Pattern) (guard : d1014 p = 1) : d55 p ≤ (6 : Int) + d55 p := by
  omega
theorem compare1913 (p : Pattern) (guard : d1014 p = 1) : d338 p ≤ (6 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d338, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1890 p hg
    simpa only [d338, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d338, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1912 p hg
    simpa only [d338, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1914 (p : Pattern) (guard : d1014 p = 1) : d65 p ≤ (6 : Int) + d65 p := by
  omega
theorem compare1915 (p : Pattern) (guard : d1014 p = 1) : d339 p ≤ (6 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d339, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1903 p hg
    simpa only [d339, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d339, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1914 p hg
    simpa only [d339, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1916 (p : Pattern) (guard : d1014 p = 1) : d340 p ≤ (6 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d340, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1913 p hg
    simpa only [d340, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d340, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1915 p hg
    simpa only [d340, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1917 (p : Pattern) (guard : d1014 p = 1) : d211 p ≤ (6 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d211, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1906 p hg
    simpa only [d211, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d211, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1912 p hg
    simpa only [d211, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1918 (p : Pattern) (guard : d1014 p = 1) : d212 p ≤ (6 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d212, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1909 p hg
    simpa only [d212, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d212, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1914 p hg
    simpa only [d212, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1919 (p : Pattern) (guard : d1014 p = 1) : d213 p ≤ (6 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d213, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1917 p hg
    simpa only [d213, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d213, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1918 p hg
    simpa only [d213, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1920 (p : Pattern) (guard : d1014 p = 1) : d341 p ≤ (6 : Int) + d834 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1916 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1919 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1921 (p : Pattern) (guard : d1014 p = 1) : d342 p ≤ (6 : Int) + d835 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d342, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1911 p hg
    simpa only [d342, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d342, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1920 p hg
    simpa only [d342, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1922 (p : Pattern) (guard : d1014 p = 1) : d66 p ≤ (6 : Int) + d66 p := by
  omega
theorem compare1923 (p : Pattern) (guard : d1014 p = 1) : d343 p ≤ (6 : Int) + d836 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d343, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1920 p hg
    simpa only [d343, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d343, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d343, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1924 (p : Pattern) (guard : d1014 p = 1) : d344 p ≤ (6 : Int) + d837 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d344, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1921 p hg
    simpa only [d344, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d344, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1923 p hg
    simpa only [d344, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1925 (p : Pattern) (guard : d1014 p = 1) : d345 p ≤ (6 : Int) + d838 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d345, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1904 p hg
    simpa only [d345, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d345, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d345, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1926 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (6 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1882 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1886 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1927 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (6 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1926 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1886 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1928 (p : Pattern) (guard : d757 p = 1) : d138 p ≤ (6 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1881 p hg
    simpa only [d757, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1927 p hg
    simpa only [d757, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1929 (p : Pattern) (guard : d1014 p = 1) : d346 p ≤ (6 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1928 p hg
    simpa only [d1014, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1889 p hg
    simpa only [d1014, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1930 (p : Pattern) (guard : d1014 p = 1) : d347 p ≤ (6 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d347, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1929 p hg
    simpa only [d347, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d347, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1912 p hg
    simpa only [d347, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1931 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (6 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1892 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1898 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1932 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (6 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1931 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1898 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1933 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (6 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1927 p hg
    simpa only [d144, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1932 p hg
    simpa only [d144, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1934 (p : Pattern) (guard : d757 p = 1) : d145 p ≤ (6 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1891 p hg
    simpa only [d757, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1933 p hg
    simpa only [d757, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1935 (p : Pattern) (guard : d1014 p = 1) : d348 p ≤ (6 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d1014, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d1014, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1936 (p : Pattern) (guard : d1014 p = 1) : d349 p ≤ (6 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d349, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1935 p hg
    simpa only [d349, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d349, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1914 p hg
    simpa only [d349, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1937 (p : Pattern) (guard : d1014 p = 1) : d350 p ≤ (6 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d350, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1930 p hg
    simpa only [d350, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d350, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1936 p hg
    simpa only [d350, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1938 (p : Pattern) (guard : d1014 p = 1) : d351 p ≤ (6 : Int) + d839 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d351, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1937 p hg
    simpa only [d351, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d351, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d351, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1939 (p : Pattern) (guard : d1014 p = 1) : d352 p ≤ (6 : Int) + d840 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d352, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1925 p hg
    simpa only [d352, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d352, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1938 p hg
    simpa only [d352, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1940 (p : Pattern) (guard : d1014 p = 1) : d353 p ≤ (6 : Int) + d839 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d353, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1916 p hg
    simpa only [d353, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d353, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d353, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1941 (p : Pattern) (guard : d1014 p = 1) : d354 p ≤ (6 : Int) + d841 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d354, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1940 p hg
    simpa only [d354, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d354, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d354, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1942 (p : Pattern) (guard : d1014 p = 1) : d355 p ≤ (6 : Int) + d842 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d355, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1939 p hg
    simpa only [d355, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d355, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1941 p hg
    simpa only [d355, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1943 (p : Pattern) (guard : d1014 p = 1) : d356 p ≤ (6 : Int) + d843 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d356, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1924 p hg
    simpa only [d356, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d356, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1942 p hg
    simpa only [d356, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1944 (p : Pattern) (guard : d798 p = 1) : d114 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d798, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare332 p hg
    simpa only [d798, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1945 (p : Pattern) (guard : d798 p = 1) : d116 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d798, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare334 p hg
    simpa only [d798, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1946 (p : Pattern) (guard : d798 p = 1) : d335 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d335, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1944 p hg
    simpa only [d335, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d335, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1945 p hg
    simpa only [d335, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1947 (p : Pattern) (guard : d798 p = 1) : d107 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1393 p hg
    simpa only [d798, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare325 p hg
    simpa only [d798, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1948 (p : Pattern) (guard : d798 p = 1) : d110 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d798, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare328 p hg
    simpa only [d798, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1949 (p : Pattern) (guard : d798 p = 1) : d336 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d336, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1947 p hg
    simpa only [d336, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d336, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1948 p hg
    simpa only [d336, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1950 (p : Pattern) (guard : d798 p = 1) : d337 p ≤ (0 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d337, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1946 p hg
    simpa only [d337, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d337, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1949 p hg
    simpa only [d337, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1951 (p : Pattern) (guard : d798 p = 1) : d338 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d798, d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1952 (p : Pattern) (guard : d798 p = 1) : d339 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d798, d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1953 (p : Pattern) (guard : d798 p = 1) : d340 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1951 p hg
    simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1952 p hg
    simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1954 (p : Pattern) (guard : d798 p = 1) : d341 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1953 p hg
    simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1955 (p : Pattern) (guard : d798 p = 1) : d342 p ≤ (0 : Int) + d315 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d342, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1950 p hg
    simpa only [d342, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d342, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1954 p hg
    simpa only [d342, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1956 (p : Pattern) (guard : d798 p = 1) : d343 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1954 p hg
    simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1957 (p : Pattern) (guard : d798 p = 1) : d344 p ≤ (0 : Int) + d316 p := by
  cases selected : p 132 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d344, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1955 p hg
    simpa only [d344, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d344, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1956 p hg
    simpa only [d344, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1958 (p : Pattern) (guard : d798 p = 1) : d345 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d345, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1946 p hg
    simpa only [d345, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d345, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d345, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1959 (p : Pattern) (guard : d798 p = 1) : d347 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1787 p hg
    simpa only [d798, d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
