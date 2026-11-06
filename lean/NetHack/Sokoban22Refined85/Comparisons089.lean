/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12460 (p : Pattern) (guard : d0 p = 1) : d353 p ≤ (0 : Int) + d1687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12461 (p : Pattern) (guard : d4967 p = 1) : d1553 p ≤ (0 : Int) + d1851 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1553, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11585 p hg
    simpa only [d4967, d1553, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1553, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12460 p hg
    simpa only [d4967, d1553, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12462 (p : Pattern) (guard : d4967 p = 1) : d1554 p ≤ (0 : Int) + d1852 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1554, d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12461 p hg
    simpa only [d1554, d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1554, d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12353 p hg
    simpa only [d1554, d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12463 (p : Pattern) (guard : d4967 p = 1) : d1555 p ≤ (0 : Int) + d1853 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1555, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12462 p hg
    simpa only [d1555, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1555, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12360 p hg
    simpa only [d1555, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12464 (p : Pattern) (guard : d4967 p = 1) : d1556 p ≤ (0 : Int) + d1854 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1556, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12463 p hg
    simpa only [d1556, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1556, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12364 p hg
    simpa only [d1556, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12465 (p : Pattern) (guard : d4967 p = 1) : d1557 p ≤ (0 : Int) + d1855 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1557, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12464 p hg
    simpa only [d1557, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1557, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12375 p hg
    simpa only [d1557, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12466 (p : Pattern) (guard : d4967 p = 1) : d1558 p ≤ (0 : Int) + d1856 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1558, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12350 p hg
    simpa only [d1558, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1558, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12380 p hg
    simpa only [d1558, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12467 (p : Pattern) (guard : d4967 p = 1) : d1559 p ≤ (0 : Int) + d1857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1559, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12466 p hg
    simpa only [d1559, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1559, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12382 p hg
    simpa only [d1559, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12468 (p : Pattern) (guard : d4967 p = 1) : d1560 p ≤ (0 : Int) + d1858 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1560, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12467 p hg
    simpa only [d1560, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1560, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12389 p hg
    simpa only [d1560, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12469 (p : Pattern) (guard : d4967 p = 1) : d1561 p ≤ (0 : Int) + d1859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1561, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12468 p hg
    simpa only [d1561, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1561, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12393 p hg
    simpa only [d1561, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12470 (p : Pattern) (guard : d4967 p = 1) : d1562 p ≤ (0 : Int) + d1860 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1562, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12465 p hg
    simpa only [d1562, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1562, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12469 p hg
    simpa only [d1562, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12471 (p : Pattern) (guard : d4967 p = 1) : d1563 p ≤ (0 : Int) + d1861 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1563, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12470 p hg
    simpa only [d1563, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1563, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12428 p hg
    simpa only [d1563, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12472 (p : Pattern) (guard : d4967 p = 1) : d1564 p ≤ (0 : Int) + d1835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1564, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12428 p hg
    simpa only [d1564, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1564, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12444 p hg
    simpa only [d1564, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12473 (p : Pattern) (guard : d4967 p = 1) : d1565 p ≤ (0 : Int) + d1862 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1565, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12471 p hg
    simpa only [d1565, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1565, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12472 p hg
    simpa only [d1565, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12474 (p : Pattern) (guard : d4967 p = 1) : d1529 p ≤ (0 : Int) + d1692 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12353 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12359 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12475 (p : Pattern) (guard : d4967 p = 1) : d1530 p ≤ (0 : Int) + d1863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1530, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12474 p hg
    simpa only [d1530, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1530, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12360 p hg
    simpa only [d1530, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12476 (p : Pattern) (guard : d4967 p = 1) : d1531 p ≤ (0 : Int) + d1864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1531, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12475 p hg
    simpa only [d1531, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1531, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12364 p hg
    simpa only [d1531, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12477 (p : Pattern) (guard : d4967 p = 1) : d1566 p ≤ (0 : Int) + d1865 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1566, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12476 p hg
    simpa only [d1566, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1566, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12375 p hg
    simpa only [d1566, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12478 (p : Pattern) (guard : d4967 p = 1) : d1567 p ≤ (0 : Int) + d1866 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1567, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12477 p hg
    simpa only [d1567, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1567, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12454 p hg
    simpa only [d1567, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12479 (p : Pattern) (guard : d4967 p = 1) : d1568 p ≤ (0 : Int) + d1867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1568, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12478 p hg
    simpa only [d1568, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1568, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12428 p hg
    simpa only [d1568, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12480 (p : Pattern) (guard : d4967 p = 1) : d1569 p ≤ (0 : Int) + d1868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1569, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12479 p hg
    simpa only [d1569, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1569, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12457 p hg
    simpa only [d1569, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12481 (p : Pattern) (guard : d4967 p = 1) : d1570 p ≤ (0 : Int) + d1869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1570, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12473 p hg
    simpa only [d1570, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1570, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12480 p hg
    simpa only [d1570, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12482 (p : Pattern) (guard : d4967 p = 1) : d1571 p ≤ (0 : Int) + d1870 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1571, d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12459 p hg
    simpa only [d1571, d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1571, d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12481 p hg
    simpa only [d1571, d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12483 (p : Pattern) (guard : d0 p = 1) : d353 p ≤ (0 : Int) + d1876 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12484 (p : Pattern) (guard : d4967 p = 1) : d1572 p ≤ (0 : Int) + d1877 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1572, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11607 p hg
    simpa only [d4967, d1572, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1572, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12483 p hg
    simpa only [d4967, d1572, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12485 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d1876 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12486 (p : Pattern) (guard : d4967 p = 1) : d1573 p ≤ (0 : Int) + d1878 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1573, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d1573, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1573, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12485 p hg
    simpa only [d4967, d1573, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12487 (p : Pattern) (guard : d4967 p = 1) : d1574 p ≤ (0 : Int) + d1879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1574, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12484 p hg
    simpa only [d1574, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1574, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12486 p hg
    simpa only [d1574, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12488 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1876 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12489 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1878 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d124, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d124, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d124, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12488 p hg
    simpa only [d4967, d124, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12490 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1884 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12491 (p : Pattern) (guard : d4967 p = 1) : d125 p ≤ (0 : Int) + d1885 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d125, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d125, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d125, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12490 p hg
    simpa only [d4967, d125, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12492 (p : Pattern) (guard : d4967 p = 1) : d126 p ≤ (0 : Int) + d1886 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d126, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12489 p hg
    simpa only [d126, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d126, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12491 p hg
    simpa only [d126, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12493 (p : Pattern) (guard : d4967 p = 1) : d1575 p ≤ (0 : Int) + d1887 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1575, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12487 p hg
    simpa only [d1575, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1575, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12492 p hg
    simpa only [d1575, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12494 (p : Pattern) (guard : d4967 p = 1) : d128 p ≤ (0 : Int) + d1888 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d128, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12385 p hg
    simpa only [d128, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d128, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d128, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12495 (p : Pattern) (guard : d4967 p = 1) : d129 p ≤ (0 : Int) + d1889 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d129, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12492 p hg
    simpa only [d129, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d129, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12494 p hg
    simpa only [d129, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12496 (p : Pattern) (guard : d4967 p = 1) : d1576 p ≤ (0 : Int) + d1890 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1576, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12493 p hg
    simpa only [d1576, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1576, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12495 p hg
    simpa only [d1576, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12497 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1899 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12498 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1900 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d124, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d124, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d124, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12497 p hg
    simpa only [d4967, d124, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12499 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1906 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12500 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1907 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d124, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d124, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d124, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12499 p hg
    simpa only [d4967, d124, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12501 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1908 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12498 p hg
    simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12500 p hg
    simpa only [d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12502 (p : Pattern) (guard : d4967 p = 1) : d1577 p ≤ (0 : Int) + d1912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1577, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12501 p hg
    simpa only [d1577, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1577, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11630 p hg
    simpa only [d1577, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12503 (p : Pattern) (guard : d4967 p = 1) : d1578 p ≤ (0 : Int) + d1914 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1578, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12502 p hg
    simpa only [d1578, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1578, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11633 p hg
    simpa only [d1578, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12504 (p : Pattern) (guard : d4967 p = 1) : d1579 p ≤ (0 : Int) + d1915 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1579, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12496 p hg
    simpa only [d1579, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1579, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12503 p hg
    simpa only [d1579, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12505 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d1876 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12506 (p : Pattern) (guard : d4967 p = 1) : d1580 p ≤ (0 : Int) + d1917 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1580, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11637 p hg
    simpa only [d4967, d1580, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1580, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12505 p hg
    simpa only [d4967, d1580, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12507 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1922 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12508 (p : Pattern) (guard : d4967 p = 1) : d139 p ≤ (0 : Int) + d1923 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d139, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d139, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d139, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12507 p hg
    simpa only [d4967, d139, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12509 (p : Pattern) (guard : d4967 p = 1) : d1581 p ≤ (0 : Int) + d1924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1581, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12506 p hg
    simpa only [d1581, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1581, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12508 p hg
    simpa only [d1581, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12510 (p : Pattern) (guard : d4967 p = 1) : d141 p ≤ (0 : Int) + d1925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d141, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12491 p hg
    simpa only [d141, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d141, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12385 p hg
    simpa only [d141, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12511 (p : Pattern) (guard : d4967 p = 1) : d1582 p ≤ (0 : Int) + d1926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1582, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12509 p hg
    simpa only [d1582, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1582, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12510 p hg
    simpa only [d1582, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12512 (p : Pattern) (guard : d4967 p = 1) : d143 p ≤ (0 : Int) + d1927 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d143, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12491 p hg
    simpa only [d143, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d143, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12387 p hg
    simpa only [d143, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12513 (p : Pattern) (guard : d4967 p = 1) : d144 p ≤ (0 : Int) + d1928 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d144, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12512 p hg
    simpa only [d144, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d144, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d144, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12514 (p : Pattern) (guard : d4967 p = 1) : d1583 p ≤ (0 : Int) + d1929 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1583, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12511 p hg
    simpa only [d1583, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1583, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12513 p hg
    simpa only [d1583, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12515 (p : Pattern) (guard : d4967 p = 1) : d1584 p ≤ (0 : Int) + d1931 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1584, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12500 p hg
    simpa only [d1584, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1584, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11649 p hg
    simpa only [d1584, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12516 (p : Pattern) (guard : d4967 p = 1) : d1585 p ≤ (0 : Int) + d1933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1585, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12515 p hg
    simpa only [d1585, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1585, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11651 p hg
    simpa only [d1585, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12517 (p : Pattern) (guard : d4967 p = 1) : d1586 p ≤ (0 : Int) + d1936 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1586, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12516 p hg
    simpa only [d1586, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1586, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11654 p hg
    simpa only [d1586, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12518 (p : Pattern) (guard : d4967 p = 1) : d1587 p ≤ (0 : Int) + d1937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1587, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12514 p hg
    simpa only [d1587, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1587, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12517 p hg
    simpa only [d1587, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12519 (p : Pattern) (guard : d4967 p = 1) : d1588 p ≤ (0 : Int) + d1938 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1588, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12504 p hg
    simpa only [d1588, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1588, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12518 p hg
    simpa only [d1588, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12520 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1943 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12521 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1944 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d124, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d124, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d124, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12520 p hg
    simpa only [d4967, d124, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12522 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1952 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12523 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1953 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d124, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d124, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d124, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12522 p hg
    simpa only [d4967, d124, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12524 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1954 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12521 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12523 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12525 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1958 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12526 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1959 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d124, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d124, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d124, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12525 p hg
    simpa only [d4967, d124, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12527 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1967 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12528 (p : Pattern) (guard : d4967 p = 1) : d125 p ≤ (0 : Int) + d1968 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d125, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d125, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d125, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12527 p hg
    simpa only [d4967, d125, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12529 (p : Pattern) (guard : d4967 p = 1) : d126 p ≤ (0 : Int) + d1969 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d126, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12526 p hg
    simpa only [d126, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d126, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12528 p hg
    simpa only [d126, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12530 (p : Pattern) (guard : d4967 p = 1) : d1577 p ≤ (0 : Int) + d1970 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1577, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12524 p hg
    simpa only [d1577, d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1577, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12529 p hg
    simpa only [d1577, d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12531 (p : Pattern) (guard : d4967 p = 1) : d129 p ≤ (0 : Int) + d1971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d129, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12529 p hg
    simpa only [d129, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d129, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12494 p hg
    simpa only [d129, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12532 (p : Pattern) (guard : d4967 p = 1) : d1578 p ≤ (0 : Int) + d1972 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1578, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12530 p hg
    simpa only [d1578, d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1578, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12531 p hg
    simpa only [d1578, d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12533 (p : Pattern) (guard : d4967 p = 1) : d139 p ≤ (0 : Int) + d1973 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d139, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d139, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d139, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12497 p hg
    simpa only [d4967, d139, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12534 (p : Pattern) (guard : d4967 p = 1) : d229 p ≤ (0 : Int) + d1974 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d229, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11673 p hg
    simpa only [d4967, d229, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d229, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12499 p hg
    simpa only [d4967, d229, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12535 (p : Pattern) (guard : d4967 p = 1) : d1053 p ≤ (0 : Int) + d1975 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1053, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12533 p hg
    simpa only [d1053, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1053, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12534 p hg
    simpa only [d1053, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12536 (p : Pattern) (guard : d4967 p = 1) : d1054 p ≤ (0 : Int) + d1976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1054, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12535 p hg
    simpa only [d1054, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1054, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1054, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12537 (p : Pattern) (guard : d4967 p = 1) : d1589 p ≤ (0 : Int) + d1977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1589, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12536 p hg
    simpa only [d1589, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1589, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1589, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12538 (p : Pattern) (guard : d4967 p = 1) : d1590 p ≤ (0 : Int) + d1978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1590, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12532 p hg
    simpa only [d1590, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1590, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12537 p hg
    simpa only [d1590, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12539 (p : Pattern) (guard : d4967 p = 1) : d1584 p ≤ (0 : Int) + d1979 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1584, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12523 p hg
    simpa only [d1584, d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1584, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12533 p hg
    simpa only [d1584, d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12540 (p : Pattern) (guard : d4967 p = 1) : d141 p ≤ (0 : Int) + d1980 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d141, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12528 p hg
    simpa only [d141, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d141, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12385 p hg
    simpa only [d141, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12541 (p : Pattern) (guard : d4967 p = 1) : d1585 p ≤ (0 : Int) + d1981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1585, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12539 p hg
    simpa only [d1585, d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1585, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12540 p hg
    simpa only [d1585, d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12542 (p : Pattern) (guard : d4967 p = 1) : d143 p ≤ (0 : Int) + d1982 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d143, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12528 p hg
    simpa only [d143, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d143, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12387 p hg
    simpa only [d143, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12543 (p : Pattern) (guard : d4967 p = 1) : d144 p ≤ (0 : Int) + d1983 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d144, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12542 p hg
    simpa only [d144, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d144, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d144, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12544 (p : Pattern) (guard : d4967 p = 1) : d1586 p ≤ (0 : Int) + d1984 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1586, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12541 p hg
    simpa only [d1586, d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1586, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12543 p hg
    simpa only [d1586, d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12545 (p : Pattern) (guard : d4967 p = 1) : d230 p ≤ (0 : Int) + d1985 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d230, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12534 p hg
    simpa only [d230, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d230, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d230, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12546 (p : Pattern) (guard : d4967 p = 1) : d231 p ≤ (0 : Int) + d1986 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d231, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12545 p hg
    simpa only [d231, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d231, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d231, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12547 (p : Pattern) (guard : d4967 p = 1) : d1591 p ≤ (0 : Int) + d1987 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1591, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12546 p hg
    simpa only [d1591, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1591, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1591, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12548 (p : Pattern) (guard : d4967 p = 1) : d1592 p ≤ (0 : Int) + d1988 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1592, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12544 p hg
    simpa only [d1592, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1592, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12547 p hg
    simpa only [d1592, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12549 (p : Pattern) (guard : d4967 p = 1) : d1593 p ≤ (0 : Int) + d1989 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1593, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12538 p hg
    simpa only [d1593, d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1593, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12548 p hg
    simpa only [d1593, d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12550 (p : Pattern) (guard : d4967 p = 1) : d1594 p ≤ (0 : Int) + d1990 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1594, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12519 p hg
    simpa only [d1594, d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1594, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12549 p hg
    simpa only [d1594, d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12551 (p : Pattern) (guard : d4967 p = 1) : d1595 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1595, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12494 p hg
    simpa only [d1595, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1595, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1595, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12552 (p : Pattern) (guard : d4967 p = 1) : d1596 p ≤ (0 : Int) + d1992 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1596, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12551 p hg
    simpa only [d1596, d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1596, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1596, d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12553 (p : Pattern) (guard : d4967 p = 1) : d1597 p ≤ (0 : Int) + d1993 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1597, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12552 p hg
    simpa only [d1597, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1597, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1597, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12554 (p : Pattern) (guard : d4967 p = 1) : d1598 p ≤ (0 : Int) + d1994 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1598, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12553 p hg
    simpa only [d1598, d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1598, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1598, d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12555 (p : Pattern) (guard : d4967 p = 1) : d1599 p ≤ (0 : Int) + d1995 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1599, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12549 p hg
    simpa only [d1599, d1995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1599, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12554 p hg
    simpa only [d1599, d1995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12556 (p : Pattern) (guard : d4967 p = 1) : d1600 p ≤ (0 : Int) + d1996 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1600, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12550 p hg
    simpa only [d1600, d1996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1600, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12555 p hg
    simpa only [d1600, d1996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12557 (p : Pattern) (guard : d4967 p = 1) : d1601 p ≤ (0 : Int) + d1878 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12486 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12489 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12558 (p : Pattern) (guard : d4967 p = 1) : d1602 p ≤ (0 : Int) + d1997 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1602, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12557 p hg
    simpa only [d1602, d1997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1602, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12492 p hg
    simpa only [d1602, d1997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12559 (p : Pattern) (guard : d4967 p = 1) : d1603 p ≤ (0 : Int) + d1998 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1603, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12558 p hg
    simpa only [d1603, d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1603, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12495 p hg
    simpa only [d1603, d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12560 (p : Pattern) (guard : d4967 p = 1) : d1604 p ≤ (0 : Int) + d1999 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1604, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12559 p hg
    simpa only [d1604, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1604, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12503 p hg
    simpa only [d1604, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12561 (p : Pattern) (guard : d4967 p = 1) : d1584 p ≤ (0 : Int) + d2000 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1584, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12489 p hg
    simpa only [d1584, d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1584, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12508 p hg
    simpa only [d1584, d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12562 (p : Pattern) (guard : d4967 p = 1) : d1585 p ≤ (0 : Int) + d2001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1585, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12561 p hg
    simpa only [d1585, d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1585, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12510 p hg
    simpa only [d1585, d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12563 (p : Pattern) (guard : d4967 p = 1) : d1586 p ≤ (0 : Int) + d2002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1586, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12562 p hg
    simpa only [d1586, d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1586, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12513 p hg
    simpa only [d1586, d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12564 (p : Pattern) (guard : d4967 p = 1) : d1586 p ≤ (0 : Int) + d2003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12563 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12517 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12565 (p : Pattern) (guard : d4967 p = 1) : d1605 p ≤ (0 : Int) + d2004 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1605, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12560 p hg
    simpa only [d1605, d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1605, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12564 p hg
    simpa only [d1605, d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12566 (p : Pattern) (guard : d4967 p = 1) : d1606 p ≤ (0 : Int) + d2005 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1606, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12565 p hg
    simpa only [d1606, d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1606, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12549 p hg
    simpa only [d1606, d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12567 (p : Pattern) (guard : d4967 p = 1) : d1607 p ≤ (0 : Int) + d2006 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1607, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12549 p hg
    simpa only [d1607, d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1607, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1607, d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12568 (p : Pattern) (guard : d4967 p = 1) : d1608 p ≤ (0 : Int) + d2007 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1608, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12566 p hg
    simpa only [d1608, d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1608, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12567 p hg
    simpa only [d1608, d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12569 (p : Pattern) (guard : d4967 p = 1) : d1609 p ≤ (0 : Int) + d2008 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1609, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12556 p hg
    simpa only [d1609, d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1609, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12568 p hg
    simpa only [d1609, d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12570 (p : Pattern) (guard : d4967 p = 1) : d1610 p ≤ (0 : Int) + d2009 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1610, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12459 p hg
    simpa only [d1610, d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1610, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12569 p hg
    simpa only [d1610, d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12571 (p : Pattern) (guard : d4967 p = 1) : d1611 p ≤ (0 : Int) + d2010 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1611, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12482 p hg
    simpa only [d1611, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1611, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12570 p hg
    simpa only [d1611, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12572 (p : Pattern) (guard : d4967 p = 1) : d1529 p ≤ (0 : Int) + d1774 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12431 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12397 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12573 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2013 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12574 (p : Pattern) (guard : d4967 p = 1) : d43 p ≤ (0 : Int) + d2014 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d43, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d4967, d43, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d43, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12573 p hg
    simpa only [d4967, d43, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12575 (p : Pattern) (guard : d4967 p = 1) : d47 p ≤ (0 : Int) + d2015 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d47, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12397 p hg
    simpa only [d47, d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d47, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12574 p hg
    simpa only [d47, d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12576 (p : Pattern) (guard : d4967 p = 1) : d1530 p ≤ (0 : Int) + d2016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1530, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12572 p hg
    simpa only [d1530, d2016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1530, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12575 p hg
    simpa only [d1530, d2016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12577 (p : Pattern) (guard : d4967 p = 1) : d50 p ≤ (0 : Int) + d2017 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d50, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12575 p hg
    simpa only [d50, d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d50, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12409 p hg
    simpa only [d50, d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12578 (p : Pattern) (guard : d4967 p = 1) : d1531 p ≤ (0 : Int) + d2018 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1531, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12576 p hg
    simpa only [d1531, d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1531, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12577 p hg
    simpa only [d1531, d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12579 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d2019 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d66, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d66, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d66, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12368 p hg
    simpa only [d4967, d66, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12580 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d2020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12412 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12579 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12581 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d2021 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d66, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d66, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d66, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12371 p hg
    simpa only [d4967, d66, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12582 (p : Pattern) (guard : d4967 p = 1) : d176 p ≤ (0 : Int) + d2023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d176, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12581 p hg
    simpa only [d176, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d176, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11720 p hg
    simpa only [d176, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12583 (p : Pattern) (guard : d4967 p = 1) : d1612 p ≤ (0 : Int) + d2024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1612, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12580 p hg
    simpa only [d1612, d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1612, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12582 p hg
    simpa only [d1612, d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12584 (p : Pattern) (guard : d4967 p = 1) : d1613 p ≤ (0 : Int) + d2027 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1613, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12583 p hg
    simpa only [d1613, d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1613, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11724 p hg
    simpa only [d1613, d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12585 (p : Pattern) (guard : d4967 p = 1) : d1614 p ≤ (0 : Int) + d2028 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1614, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12578 p hg
    simpa only [d1614, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1614, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12584 p hg
    simpa only [d1614, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12586 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2031 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12587 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d2032 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d66, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d66, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d66, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12586 p hg
    simpa only [d4967, d66, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12588 (p : Pattern) (guard : d4967 p = 1) : d1518 p ≤ (0 : Int) + d2033 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1518, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12397 p hg
    simpa only [d1518, d2033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1518, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12587 p hg
    simpa only [d1518, d2033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12589 (p : Pattern) (guard : d4967 p = 1) : d68 p ≤ (0 : Int) + d2034 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d68, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12574 p hg
    simpa only [d68, d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d68, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12408 p hg
    simpa only [d68, d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12590 (p : Pattern) (guard : d4967 p = 1) : d1519 p ≤ (0 : Int) + d2035 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1519, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12588 p hg
    simpa only [d1519, d2035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1519, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12589 p hg
    simpa only [d1519, d2035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12591 (p : Pattern) (guard : d4967 p = 1) : d71 p ≤ (0 : Int) + d2036 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d71, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12574 p hg
    simpa only [d71, d2036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d71, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12385 p hg
    simpa only [d71, d2036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12592 (p : Pattern) (guard : d4967 p = 1) : d74 p ≤ (0 : Int) + d2037 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d74, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12591 p hg
    simpa only [d74, d2037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d74, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12388 p hg
    simpa only [d74, d2037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12593 (p : Pattern) (guard : d4967 p = 1) : d1520 p ≤ (0 : Int) + d2038 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1520, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12590 p hg
    simpa only [d1520, d2038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1520, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12592 p hg
    simpa only [d1520, d2038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12594 (p : Pattern) (guard : d4967 p = 1) : d1615 p ≤ (0 : Int) + d2039 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1615, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12579 p hg
    simpa only [d1615, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1615, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d1615, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12595 (p : Pattern) (guard : d4967 p = 1) : d1616 p ≤ (0 : Int) + d2041 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1616, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12594 p hg
    simpa only [d1616, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1616, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11736 p hg
    simpa only [d1616, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12596 (p : Pattern) (guard : d4967 p = 1) : d1617 p ≤ (0 : Int) + d2044 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1617, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12595 p hg
    simpa only [d1617, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1617, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11739 p hg
    simpa only [d1617, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12597 (p : Pattern) (guard : d4967 p = 1) : d1618 p ≤ (0 : Int) + d2045 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1618, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12593 p hg
    simpa only [d1618, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1618, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12596 p hg
    simpa only [d1618, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12598 (p : Pattern) (guard : d4967 p = 1) : d1619 p ≤ (0 : Int) + d2046 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1619, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12585 p hg
    simpa only [d1619, d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1619, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12597 p hg
    simpa only [d1619, d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12599 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2049 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
