/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons109
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15400 (p : Pattern) (guard : d4967 p = 1) : d1858 p ≤ (0 : Int) + d1560 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1858, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15399 p hg
    simpa only [d1858, d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1858, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15312 p hg
    simpa only [d1858, d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15401 (p : Pattern) (guard : d4967 p = 1) : d1859 p ≤ (0 : Int) + d1561 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1859, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15400 p hg
    simpa only [d1859, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1859, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15323 p hg
    simpa only [d1859, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15402 (p : Pattern) (guard : d4967 p = 1) : d1860 p ≤ (0 : Int) + d1562 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1860, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15397 p hg
    simpa only [d1860, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1860, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15401 p hg
    simpa only [d1860, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15403 (p : Pattern) (guard : d4967 p = 1) : d1861 p ≤ (0 : Int) + d1563 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1861, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15402 p hg
    simpa only [d1861, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1861, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15358 p hg
    simpa only [d1861, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15404 (p : Pattern) (guard : d4967 p = 1) : d1835 p ≤ (0 : Int) + d1564 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1835, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15358 p hg
    simpa only [d1835, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1835, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15374 p hg
    simpa only [d1835, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15405 (p : Pattern) (guard : d4967 p = 1) : d1862 p ≤ (0 : Int) + d1565 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1862, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15403 p hg
    simpa only [d1862, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1862, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15404 p hg
    simpa only [d1862, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15406 (p : Pattern) (guard : d4967 p = 1) : d1692 p ≤ (0 : Int) + d1529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15268 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15274 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15407 (p : Pattern) (guard : d4967 p = 1) : d1863 p ≤ (0 : Int) + d1530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1863, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15406 p hg
    simpa only [d1863, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1863, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15275 p hg
    simpa only [d1863, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15408 (p : Pattern) (guard : d4967 p = 1) : d1864 p ≤ (0 : Int) + d1531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1864, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15407 p hg
    simpa only [d1864, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1864, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15279 p hg
    simpa only [d1864, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15409 (p : Pattern) (guard : d4967 p = 1) : d1865 p ≤ (0 : Int) + d1566 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1865, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15408 p hg
    simpa only [d1865, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1865, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15296 p hg
    simpa only [d1865, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15410 (p : Pattern) (guard : d4967 p = 1) : d1866 p ≤ (0 : Int) + d1567 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1866, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15409 p hg
    simpa only [d1866, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1866, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15384 p hg
    simpa only [d1866, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15411 (p : Pattern) (guard : d4967 p = 1) : d1867 p ≤ (0 : Int) + d1568 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1867, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15410 p hg
    simpa only [d1867, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1867, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15358 p hg
    simpa only [d1867, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15412 (p : Pattern) (guard : d4967 p = 1) : d1868 p ≤ (0 : Int) + d1569 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1868, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15411 p hg
    simpa only [d1868, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1868, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15387 p hg
    simpa only [d1868, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15413 (p : Pattern) (guard : d4967 p = 1) : d1869 p ≤ (0 : Int) + d1570 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1869, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15405 p hg
    simpa only [d1869, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1869, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15412 p hg
    simpa only [d1869, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15414 (p : Pattern) (guard : d4967 p = 1) : d1870 p ≤ (0 : Int) + d1571 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1870, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15389 p hg
    simpa only [d1870, d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1870, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15413 p hg
    simpa only [d1870, d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15415 (p : Pattern) (guard : d0 p = 1) : d358 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15416 (p : Pattern) (guard : d4474 p = 1) : d1871 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15415 p hg
    simpa only [d4474, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15417 (p : Pattern) (guard : d0 p = 1) : d1876 p ≤ (0 : Int) + d353 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15418 (p : Pattern) (guard : d4967 p = 1) : d1877 p ≤ (0 : Int) + d1572 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1877, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15416 p hg
    simpa only [d4967, d1877, d1572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1877, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15417 p hg
    simpa only [d4967, d1877, d1572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15419 (p : Pattern) (guard : d0 p = 1) : d1876 p ≤ (0 : Int) + d343 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15420 (p : Pattern) (guard : d4967 p = 1) : d1878 p ≤ (0 : Int) + d1573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1878, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1878, d1573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1878, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15419 p hg
    simpa only [d4967, d1878, d1573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15421 (p : Pattern) (guard : d4967 p = 1) : d1879 p ≤ (0 : Int) + d1574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1879, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15418 p hg
    simpa only [d1879, d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1879, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15420 p hg
    simpa only [d1879, d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15422 (p : Pattern) (guard : d0 p = 1) : d1876 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15423 (p : Pattern) (guard : d4967 p = 1) : d1878 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1878, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1878, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1878, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15422 p hg
    simpa only [d4967, d1878, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15424 (p : Pattern) (guard : d0 p = 1) : d1884 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15425 (p : Pattern) (guard : d4967 p = 1) : d1885 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1885, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d1885, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1885, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d4967, d1885, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15426 (p : Pattern) (guard : d4967 p = 1) : d1886 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1886, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15423 p hg
    simpa only [d1886, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1886, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15425 p hg
    simpa only [d1886, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15427 (p : Pattern) (guard : d4967 p = 1) : d1887 p ≤ (0 : Int) + d1575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1887, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15421 p hg
    simpa only [d1887, d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1887, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15426 p hg
    simpa only [d1887, d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15428 (p : Pattern) (guard : d4967 p = 1) : d1888 p ≤ (0 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1888, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15308 p hg
    simpa only [d1888, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1888, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1888, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15429 (p : Pattern) (guard : d4967 p = 1) : d1889 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1889, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15426 p hg
    simpa only [d1889, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1889, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15428 p hg
    simpa only [d1889, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15430 (p : Pattern) (guard : d4967 p = 1) : d1890 p ≤ (0 : Int) + d1576 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1890, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15427 p hg
    simpa only [d1890, d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1890, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15429 p hg
    simpa only [d1890, d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15431 (p : Pattern) (guard : d0 p = 1) : d1899 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15432 (p : Pattern) (guard : d4967 p = 1) : d1900 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1900, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1900, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1900, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d4967, d1900, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15433 (p : Pattern) (guard : d0 p = 1) : d1906 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15434 (p : Pattern) (guard : d4967 p = 1) : d1907 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1907, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1907, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1907, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d4967, d1907, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15435 (p : Pattern) (guard : d4967 p = 1) : d1908 p ≤ (0 : Int) + d124 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15432 p hg
    simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15434 p hg
    simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15436 (p : Pattern) (guard : d4967 p = 1) : d1909 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1909, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1909, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1909, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d1909, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15437 (p : Pattern) (guard : d4967 p = 1) : d1910 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1910, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d1910, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1910, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d1910, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15438 (p : Pattern) (guard : d4967 p = 1) : d1911 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1911, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15436 p hg
    simpa only [d1911, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1911, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15437 p hg
    simpa only [d1911, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15439 (p : Pattern) (guard : d4967 p = 1) : d1912 p ≤ (0 : Int) + d1577 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1912, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15435 p hg
    simpa only [d1912, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1912, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15438 p hg
    simpa only [d1912, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15440 (p : Pattern) (guard : d4967 p = 1) : d278 p ≤ (0 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15318 p hg
    simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15441 (p : Pattern) (guard : d4967 p = 1) : d1913 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1913, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15438 p hg
    simpa only [d1913, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1913, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15440 p hg
    simpa only [d1913, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15442 (p : Pattern) (guard : d4967 p = 1) : d1914 p ≤ (0 : Int) + d1578 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1914, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15439 p hg
    simpa only [d1914, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1914, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15441 p hg
    simpa only [d1914, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15443 (p : Pattern) (guard : d4967 p = 1) : d1915 p ≤ (0 : Int) + d1579 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1915, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15430 p hg
    simpa only [d1915, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1915, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15442 p hg
    simpa only [d1915, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15444 (p : Pattern) (guard : d0 p = 1) : d333 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15445 (p : Pattern) (guard : d4474 p = 1) : d1916 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15444 p hg
    simpa only [d4474, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15446 (p : Pattern) (guard : d0 p = 1) : d1876 p ≤ (0 : Int) + d336 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15447 (p : Pattern) (guard : d4967 p = 1) : d1917 p ≤ (0 : Int) + d1580 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1917, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15445 p hg
    simpa only [d4967, d1917, d1580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1917, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15446 p hg
    simpa only [d4967, d1917, d1580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15448 (p : Pattern) (guard : d0 p = 1) : d1922 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15449 (p : Pattern) (guard : d4967 p = 1) : d1923 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1923, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d1923, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1923, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15448 p hg
    simpa only [d4967, d1923, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15450 (p : Pattern) (guard : d4967 p = 1) : d1924 p ≤ (0 : Int) + d1581 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1924, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15447 p hg
    simpa only [d1924, d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1924, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15449 p hg
    simpa only [d1924, d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15451 (p : Pattern) (guard : d4967 p = 1) : d1925 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1925, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15425 p hg
    simpa only [d1925, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1925, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15308 p hg
    simpa only [d1925, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15452 (p : Pattern) (guard : d4967 p = 1) : d1926 p ≤ (0 : Int) + d1582 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1926, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15450 p hg
    simpa only [d1926, d1582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1926, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15451 p hg
    simpa only [d1926, d1582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15453 (p : Pattern) (guard : d4967 p = 1) : d1927 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1927, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15425 p hg
    simpa only [d1927, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1927, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15310 p hg
    simpa only [d1927, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15454 (p : Pattern) (guard : d4967 p = 1) : d1928 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1928, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15453 p hg
    simpa only [d1928, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1928, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1928, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15455 (p : Pattern) (guard : d4967 p = 1) : d1929 p ≤ (0 : Int) + d1583 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1929, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15452 p hg
    simpa only [d1929, d1583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1929, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15454 p hg
    simpa only [d1929, d1583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15456 (p : Pattern) (guard : d4967 p = 1) : d1930 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1930, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d1930, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1930, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d1930, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15457 (p : Pattern) (guard : d4967 p = 1) : d1931 p ≤ (0 : Int) + d1584 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1931, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15434 p hg
    simpa only [d1931, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1931, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15456 p hg
    simpa only [d1931, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15458 (p : Pattern) (guard : d4967 p = 1) : d1932 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1932, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15437 p hg
    simpa only [d1932, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1932, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15318 p hg
    simpa only [d1932, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15459 (p : Pattern) (guard : d4967 p = 1) : d1933 p ≤ (0 : Int) + d1585 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1933, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15457 p hg
    simpa only [d1933, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1933, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15458 p hg
    simpa only [d1933, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15460 (p : Pattern) (guard : d4967 p = 1) : d1934 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1934, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15437 p hg
    simpa only [d1934, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1934, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15320 p hg
    simpa only [d1934, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15461 (p : Pattern) (guard : d4967 p = 1) : d1935 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1935, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15460 p hg
    simpa only [d1935, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1935, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1935, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15462 (p : Pattern) (guard : d4967 p = 1) : d1936 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1936, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15459 p hg
    simpa only [d1936, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1936, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15461 p hg
    simpa only [d1936, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15463 (p : Pattern) (guard : d4967 p = 1) : d1937 p ≤ (0 : Int) + d1587 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1937, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15455 p hg
    simpa only [d1937, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1937, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15462 p hg
    simpa only [d1937, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15464 (p : Pattern) (guard : d4967 p = 1) : d1938 p ≤ (0 : Int) + d1588 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1938, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15443 p hg
    simpa only [d1938, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1938, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15463 p hg
    simpa only [d1938, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15465 (p : Pattern) (guard : d0 p = 1) : d1943 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15466 (p : Pattern) (guard : d4967 p = 1) : d1944 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1944, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1944, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1944, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15465 p hg
    simpa only [d4967, d1944, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15467 (p : Pattern) (guard : d0 p = 1) : d1952 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15468 (p : Pattern) (guard : d4967 p = 1) : d1953 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1953, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1953, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1953, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d4967, d1953, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15469 (p : Pattern) (guard : d4967 p = 1) : d1954 p ≤ (0 : Int) + d124 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15466 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15468 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15470 (p : Pattern) (guard : d0 p = 1) : d1958 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15471 (p : Pattern) (guard : d4967 p = 1) : d1959 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1959, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1959, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1959, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d4967, d1959, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15472 (p : Pattern) (guard : d0 p = 1) : d1967 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15473 (p : Pattern) (guard : d4967 p = 1) : d1968 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1968, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d1968, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1968, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15472 p hg
    simpa only [d4967, d1968, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15474 (p : Pattern) (guard : d4967 p = 1) : d1969 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1969, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15471 p hg
    simpa only [d1969, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1969, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d1969, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15475 (p : Pattern) (guard : d4967 p = 1) : d1970 p ≤ (0 : Int) + d1577 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1970, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15469 p hg
    simpa only [d1970, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1970, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15474 p hg
    simpa only [d1970, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15476 (p : Pattern) (guard : d4967 p = 1) : d1971 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1971, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15474 p hg
    simpa only [d1971, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1971, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15428 p hg
    simpa only [d1971, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15477 (p : Pattern) (guard : d4967 p = 1) : d1972 p ≤ (0 : Int) + d1578 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1972, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15475 p hg
    simpa only [d1972, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1972, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15476 p hg
    simpa only [d1972, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15478 (p : Pattern) (guard : d4967 p = 1) : d1973 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1973, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d1973, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1973, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d4967, d1973, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15479 (p : Pattern) (guard : d4967 p = 1) : d1974 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1974, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5855 p hg
    simpa only [d4967, d1974, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1974, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d4967, d1974, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15480 (p : Pattern) (guard : d4967 p = 1) : d1975 p ≤ (0 : Int) + d1053 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1975, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d1975, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1975, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15479 p hg
    simpa only [d1975, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15481 (p : Pattern) (guard : d4967 p = 1) : d1976 p ≤ (0 : Int) + d1054 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1976, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15480 p hg
    simpa only [d1976, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1976, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1976, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15482 (p : Pattern) (guard : d4967 p = 1) : d1977 p ≤ (0 : Int) + d1589 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1977, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15481 p hg
    simpa only [d1977, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1977, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1977, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15483 (p : Pattern) (guard : d4967 p = 1) : d1978 p ≤ (0 : Int) + d1590 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1978, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15477 p hg
    simpa only [d1978, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1978, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15482 p hg
    simpa only [d1978, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15484 (p : Pattern) (guard : d4967 p = 1) : d1979 p ≤ (0 : Int) + d1584 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1979, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15468 p hg
    simpa only [d1979, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1979, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d1979, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15485 (p : Pattern) (guard : d4967 p = 1) : d1980 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1980, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d1980, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1980, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15308 p hg
    simpa only [d1980, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15486 (p : Pattern) (guard : d4967 p = 1) : d1981 p ≤ (0 : Int) + d1585 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1981, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15484 p hg
    simpa only [d1981, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1981, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15485 p hg
    simpa only [d1981, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15487 (p : Pattern) (guard : d4967 p = 1) : d1982 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1982, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d1982, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1982, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15310 p hg
    simpa only [d1982, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15488 (p : Pattern) (guard : d4967 p = 1) : d1983 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1983, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15487 p hg
    simpa only [d1983, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1983, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1983, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15489 (p : Pattern) (guard : d4967 p = 1) : d1984 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1984, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15486 p hg
    simpa only [d1984, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1984, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15488 p hg
    simpa only [d1984, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15490 (p : Pattern) (guard : d4967 p = 1) : d1985 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1985, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15479 p hg
    simpa only [d1985, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1985, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1985, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15491 (p : Pattern) (guard : d4967 p = 1) : d1986 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1986, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15490 p hg
    simpa only [d1986, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1986, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1986, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15492 (p : Pattern) (guard : d4967 p = 1) : d1987 p ≤ (0 : Int) + d1591 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1987, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15491 p hg
    simpa only [d1987, d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1987, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1987, d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15493 (p : Pattern) (guard : d4967 p = 1) : d1988 p ≤ (0 : Int) + d1592 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1988, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15489 p hg
    simpa only [d1988, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1988, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15492 p hg
    simpa only [d1988, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15494 (p : Pattern) (guard : d4967 p = 1) : d1989 p ≤ (0 : Int) + d1593 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1989, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15483 p hg
    simpa only [d1989, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1989, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15493 p hg
    simpa only [d1989, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15495 (p : Pattern) (guard : d4967 p = 1) : d1990 p ≤ (0 : Int) + d1594 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1990, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15464 p hg
    simpa only [d1990, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1990, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15494 p hg
    simpa only [d1990, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15496 (p : Pattern) (guard : d4967 p = 1) : d1991 p ≤ (0 : Int) + d1595 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1991, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15428 p hg
    simpa only [d1991, d1595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1991, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1991, d1595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15497 (p : Pattern) (guard : d4967 p = 1) : d1992 p ≤ (0 : Int) + d1596 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1992, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15496 p hg
    simpa only [d1992, d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1992, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1992, d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15498 (p : Pattern) (guard : d4967 p = 1) : d1993 p ≤ (0 : Int) + d1597 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1993, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15497 p hg
    simpa only [d1993, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1993, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1993, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15499 (p : Pattern) (guard : d4967 p = 1) : d1994 p ≤ (0 : Int) + d1598 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1994, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15498 p hg
    simpa only [d1994, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1994, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1994, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15500 (p : Pattern) (guard : d4967 p = 1) : d1995 p ≤ (0 : Int) + d1599 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1995, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15494 p hg
    simpa only [d1995, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1995, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15499 p hg
    simpa only [d1995, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15501 (p : Pattern) (guard : d4967 p = 1) : d1996 p ≤ (0 : Int) + d1600 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1996, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15495 p hg
    simpa only [d1996, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1996, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15500 p hg
    simpa only [d1996, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15502 (p : Pattern) (guard : d4967 p = 1) : d1878 p ≤ (0 : Int) + d1601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15420 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15423 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15503 (p : Pattern) (guard : d4967 p = 1) : d1997 p ≤ (0 : Int) + d1602 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1997, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15502 p hg
    simpa only [d1997, d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1997, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15426 p hg
    simpa only [d1997, d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15504 (p : Pattern) (guard : d4967 p = 1) : d1998 p ≤ (0 : Int) + d1603 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1998, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15503 p hg
    simpa only [d1998, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1998, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15429 p hg
    simpa only [d1998, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15505 (p : Pattern) (guard : d4967 p = 1) : d1999 p ≤ (0 : Int) + d1604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1999, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15504 p hg
    simpa only [d1999, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1999, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15442 p hg
    simpa only [d1999, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15506 (p : Pattern) (guard : d4967 p = 1) : d2000 p ≤ (0 : Int) + d1584 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2000, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15423 p hg
    simpa only [d2000, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2000, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15449 p hg
    simpa only [d2000, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15507 (p : Pattern) (guard : d4967 p = 1) : d2001 p ≤ (0 : Int) + d1585 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2001, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15506 p hg
    simpa only [d2001, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2001, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15451 p hg
    simpa only [d2001, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15508 (p : Pattern) (guard : d4967 p = 1) : d2002 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2002, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15507 p hg
    simpa only [d2002, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2002, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15454 p hg
    simpa only [d2002, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15509 (p : Pattern) (guard : d4967 p = 1) : d2003 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15508 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15462 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15510 (p : Pattern) (guard : d4967 p = 1) : d2004 p ≤ (0 : Int) + d1605 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2004, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15505 p hg
    simpa only [d2004, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2004, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15509 p hg
    simpa only [d2004, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15511 (p : Pattern) (guard : d4967 p = 1) : d2005 p ≤ (0 : Int) + d1606 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2005, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15510 p hg
    simpa only [d2005, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2005, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15494 p hg
    simpa only [d2005, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15512 (p : Pattern) (guard : d4967 p = 1) : d2006 p ≤ (0 : Int) + d1607 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2006, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15494 p hg
    simpa only [d2006, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2006, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2006, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15513 (p : Pattern) (guard : d4967 p = 1) : d2007 p ≤ (0 : Int) + d1608 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2007, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15511 p hg
    simpa only [d2007, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2007, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15512 p hg
    simpa only [d2007, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15514 (p : Pattern) (guard : d4967 p = 1) : d2008 p ≤ (0 : Int) + d1609 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2008, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15501 p hg
    simpa only [d2008, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2008, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15513 p hg
    simpa only [d2008, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15515 (p : Pattern) (guard : d4967 p = 1) : d2009 p ≤ (0 : Int) + d1610 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2009, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15389 p hg
    simpa only [d2009, d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2009, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15514 p hg
    simpa only [d2009, d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15516 (p : Pattern) (guard : d4967 p = 1) : d2010 p ≤ (0 : Int) + d1611 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2010, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15414 p hg
    simpa only [d2010, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2010, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15515 p hg
    simpa only [d2010, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15517 (p : Pattern) (guard : d4967 p = 1) : d1774 p ≤ (0 : Int) + d1529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15361 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15327 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15518 (p : Pattern) (guard : d0 p = 1) : d2013 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15519 (p : Pattern) (guard : d4967 p = 1) : d2014 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2014, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d4967, d2014, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2014, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15518 p hg
    simpa only [d4967, d2014, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15520 (p : Pattern) (guard : d4967 p = 1) : d2015 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2015, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15327 p hg
    simpa only [d2015, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2015, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15519 p hg
    simpa only [d2015, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15521 (p : Pattern) (guard : d4967 p = 1) : d2016 p ≤ (0 : Int) + d1530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2016, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15517 p hg
    simpa only [d2016, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2016, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15520 p hg
    simpa only [d2016, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15522 (p : Pattern) (guard : d4967 p = 1) : d2017 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2017, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15520 p hg
    simpa only [d2017, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2017, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15339 p hg
    simpa only [d2017, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15523 (p : Pattern) (guard : d4967 p = 1) : d2018 p ≤ (0 : Int) + d1531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2018, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15521 p hg
    simpa only [d2018, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2018, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15522 p hg
    simpa only [d2018, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15524 (p : Pattern) (guard : d4967 p = 1) : d2019 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2019, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d2019, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2019, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d4967, d2019, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15525 (p : Pattern) (guard : d4967 p = 1) : d2020 p ≤ (0 : Int) + d66 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15342 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15524 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15526 (p : Pattern) (guard : d4967 p = 1) : d2021 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2021, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d2021, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2021, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d4967, d2021, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15527 (p : Pattern) (guard : d4967 p = 1) : d2022 p ≤ (0 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2022, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d4967, d2022, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2022, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d2022, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15528 (p : Pattern) (guard : d4967 p = 1) : d2023 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2023, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15526 p hg
    simpa only [d2023, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2023, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15527 p hg
    simpa only [d2023, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15529 (p : Pattern) (guard : d4967 p = 1) : d2024 p ≤ (0 : Int) + d1612 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2024, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15525 p hg
    simpa only [d2024, d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2024, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15528 p hg
    simpa only [d2024, d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15530 (p : Pattern) (guard : d4967 p = 1) : d2025 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2025, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15314 p hg
    simpa only [d2025, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2025, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15527 p hg
    simpa only [d2025, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15531 (p : Pattern) (guard : d4967 p = 1) : d2026 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2026, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15530 p hg
    simpa only [d2026, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2026, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15321 p hg
    simpa only [d2026, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15532 (p : Pattern) (guard : d4967 p = 1) : d2027 p ≤ (0 : Int) + d1613 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2027, d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15529 p hg
    simpa only [d2027, d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2027, d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15531 p hg
    simpa only [d2027, d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15533 (p : Pattern) (guard : d4967 p = 1) : d2028 p ≤ (0 : Int) + d1614 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2028, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15523 p hg
    simpa only [d2028, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2028, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15532 p hg
    simpa only [d2028, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15534 (p : Pattern) (guard : d0 p = 1) : d2031 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15535 (p : Pattern) (guard : d4967 p = 1) : d2032 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2032, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d2032, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2032, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15534 p hg
    simpa only [d4967, d2032, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15536 (p : Pattern) (guard : d4967 p = 1) : d2033 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2033, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15327 p hg
    simpa only [d2033, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2033, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15535 p hg
    simpa only [d2033, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15537 (p : Pattern) (guard : d4967 p = 1) : d2034 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2034, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15519 p hg
    simpa only [d2034, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2034, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15338 p hg
    simpa only [d2034, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15538 (p : Pattern) (guard : d4967 p = 1) : d2035 p ≤ (0 : Int) + d1519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2035, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15536 p hg
    simpa only [d2035, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2035, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15537 p hg
    simpa only [d2035, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15539 (p : Pattern) (guard : d4967 p = 1) : d2036 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2036, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15519 p hg
    simpa only [d2036, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2036, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15308 p hg
    simpa only [d2036, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
