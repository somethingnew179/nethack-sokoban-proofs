/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25340 (p : Pattern) (guard : d5540 p = 1) : d2012 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25338 p hg
    simpa only [d5540, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25339 p hg
    simpa only [d5540, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25341 (p : Pattern) (guard : d5540 p = 1) : d2897 p ≤ (2 : Int) + d6047 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2897, d6047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25336 p hg
    simpa only [d2897, d6047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2897, d6047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25340 p hg
    simpa only [d2897, d6047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25342 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (2 : Int) + d1694 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25343 (p : Pattern) (guard : d1 p = 1) : d1694 p ≤ (2 : Int) + d1694 p := by
  omega
theorem compare25344 (p : Pattern) (guard : d5501 p = 1) : d1695 p ≤ (2 : Int) + d1694 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25342 p hg
    simpa only [d5501, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25343 p hg
    simpa only [d5501, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25345 (p : Pattern) (guard : d0 p = 1) : d1694 p ≤ (2 : Int) + d1694 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25346 (p : Pattern) (guard : d5540 p = 1) : d1696 p ≤ (2 : Int) + d1694 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25344 p hg
    simpa only [d5540, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25345 p hg
    simpa only [d5540, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25347 (p : Pattern) (guard : d5540 p = 1) : d1697 p ≤ (2 : Int) + d6048 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1697, d6048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25346 p hg
    simpa only [d1697, d6048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1697, d6048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1697, d6048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25348 (p : Pattern) (guard : d5540 p = 1) : d2898 p ≤ (2 : Int) + d6049 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2898, d6049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25341 p hg
    simpa only [d2898, d6049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2898, d6049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25347 p hg
    simpa only [d2898, d6049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25349 (p : Pattern) (guard : d5540 p = 1) : d2899 p ≤ (2 : Int) + d6050 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2899, d6050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25335 p hg
    simpa only [d2899, d6050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2899, d6050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25348 p hg
    simpa only [d2899, d6050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25350 (p : Pattern) (guard : d5540 p = 1) : d2900 p ≤ (2 : Int) + d6051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2900, d6051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25335 p hg
    simpa only [d2900, d6051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2900, d6051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25349 p hg
    simpa only [d2900, d6051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25351 (p : Pattern) (guard : d5540 p = 1) : d24 p ≤ (2 : Int) + d24 p := by
  omega
theorem compare25352 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (2 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25353 (p : Pattern) (guard : d1 p = 1) : d356 p ≤ (2 : Int) + d356 p := by
  omega
theorem compare25354 (p : Pattern) (guard : d5501 p = 1) : d1802 p ≤ (2 : Int) + d356 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25352 p hg
    simpa only [d5501, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25353 p hg
    simpa only [d5501, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25355 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (2 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25356 (p : Pattern) (guard : d5540 p = 1) : d1803 p ≤ (2 : Int) + d356 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25354 p hg
    simpa only [d5540, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25355 p hg
    simpa only [d5540, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25357 (p : Pattern) (guard : d5540 p = 1) : d2901 p ≤ (2 : Int) + d6052 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2901, d6052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25351 p hg
    simpa only [d2901, d6052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2901, d6052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25356 p hg
    simpa only [d2901, d6052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25358 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (2 : Int) + d1702 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25359 (p : Pattern) (guard : d1 p = 1) : d1702 p ≤ (2 : Int) + d1702 p := by
  omega
theorem compare25360 (p : Pattern) (guard : d5501 p = 1) : d1703 p ≤ (2 : Int) + d1702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25358 p hg
    simpa only [d5501, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25359 p hg
    simpa only [d5501, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25361 (p : Pattern) (guard : d0 p = 1) : d1702 p ≤ (2 : Int) + d1702 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25362 (p : Pattern) (guard : d5540 p = 1) : d1704 p ≤ (2 : Int) + d1702 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25360 p hg
    simpa only [d5540, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25361 p hg
    simpa only [d5540, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25363 (p : Pattern) (guard : d5540 p = 1) : d1705 p ≤ (2 : Int) + d6053 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1705, d6053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25362 p hg
    simpa only [d1705, d6053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1705, d6053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1705, d6053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25364 (p : Pattern) (guard : d5540 p = 1) : d2902 p ≤ (2 : Int) + d6054 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2902, d6054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25357 p hg
    simpa only [d2902, d6054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2902, d6054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25363 p hg
    simpa only [d2902, d6054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25365 (p : Pattern) (guard : d5540 p = 1) : d2903 p ≤ (2 : Int) + d6055 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2903, d6055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25364 p hg
    simpa only [d2903, d6055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2903, d6055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2903, d6055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25366 (p : Pattern) (guard : d5540 p = 1) : d2904 p ≤ (2 : Int) + d6056 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2904, d6056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25349 p hg
    simpa only [d2904, d6056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2904, d6056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25365 p hg
    simpa only [d2904, d6056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25367 (p : Pattern) (guard : d5540 p = 1) : d2905 p ≤ (2 : Int) + d6057 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2905, d6057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25350 p hg
    simpa only [d2905, d6057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2905, d6057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25366 p hg
    simpa only [d2905, d6057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25368 (p : Pattern) (guard : d5501 p = 1) : d1777 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25323 p hg
    simpa only [d5501, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24406 p hg
    simpa only [d5501, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25369 (p : Pattern) (guard : d0 p = 1) : d1787 p ≤ (2 : Int) + d1770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25370 (p : Pattern) (guard : d5540 p = 1) : d1788 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25368 p hg
    simpa only [d5540, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25369 p hg
    simpa only [d5540, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25371 (p : Pattern) (guard : d5540 p = 1) : d2906 p ≤ (2 : Int) + d6044 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2906, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25322 p hg
    simpa only [d2906, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2906, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25370 p hg
    simpa only [d2906, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25372 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d1714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25373 (p : Pattern) (guard : d5501 p = 1) : d1712 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25372 p hg
    simpa only [d5501, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24689 p hg
    simpa only [d5501, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25374 (p : Pattern) (guard : d0 p = 1) : d1716 p ≤ (2 : Int) + d1714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25375 (p : Pattern) (guard : d5540 p = 1) : d1717 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25373 p hg
    simpa only [d5540, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25374 p hg
    simpa only [d5540, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25376 (p : Pattern) (guard : d5540 p = 1) : d1718 p ≤ (2 : Int) + d6058 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1718, d6058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25375 p hg
    simpa only [d1718, d6058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1718, d6058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1718, d6058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25377 (p : Pattern) (guard : d5540 p = 1) : d2907 p ≤ (2 : Int) + d6059 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2907, d6059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25371 p hg
    simpa only [d2907, d6059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2907, d6059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25376 p hg
    simpa only [d2907, d6059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25378 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (2 : Int) + d1722 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25379 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d1721 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d34, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d34, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25380 (p : Pattern) (guard : d1 p = 1) : d364 p ≤ (2 : Int) + d1722 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d364, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25379 p hg
    simpa only [d364, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d364, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2177 p hg
    simpa only [d364, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25381 (p : Pattern) (guard : d5501 p = 1) : d1720 p ≤ (2 : Int) + d1722 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25378 p hg
    simpa only [d5501, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25380 p hg
    simpa only [d5501, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25382 (p : Pattern) (guard : d0 p = 1) : d1723 p ≤ (2 : Int) + d1722 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25383 (p : Pattern) (guard : d5540 p = 1) : d1724 p ≤ (2 : Int) + d1722 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25381 p hg
    simpa only [d5540, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25382 p hg
    simpa only [d5540, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25384 (p : Pattern) (guard : d5540 p = 1) : d1725 p ≤ (2 : Int) + d6060 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1725, d6060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25383 p hg
    simpa only [d1725, d6060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1725, d6060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1725, d6060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25385 (p : Pattern) (guard : d5540 p = 1) : d2908 p ≤ (2 : Int) + d6061 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2908, d6061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25371 p hg
    simpa only [d2908, d6061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2908, d6061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25384 p hg
    simpa only [d2908, d6061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25386 (p : Pattern) (guard : d5540 p = 1) : d2909 p ≤ (2 : Int) + d6062 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2909, d6062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25377 p hg
    simpa only [d2909, d6062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2909, d6062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25385 p hg
    simpa only [d2909, d6062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25387 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (2 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25388 (p : Pattern) (guard : d1 p = 1) : d327 p ≤ (2 : Int) + d327 p := by
  omega
theorem compare25389 (p : Pattern) (guard : d5501 p = 1) : d1728 p ≤ (2 : Int) + d327 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25387 p hg
    simpa only [d5501, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25388 p hg
    simpa only [d5501, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25390 (p : Pattern) (guard : d0 p = 1) : d327 p ≤ (2 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25391 (p : Pattern) (guard : d5540 p = 1) : d1729 p ≤ (2 : Int) + d327 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25389 p hg
    simpa only [d5540, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25390 p hg
    simpa only [d5540, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25392 (p : Pattern) (guard : d5540 p = 1) : d1730 p ≤ (2 : Int) + d6063 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1730, d6063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25391 p hg
    simpa only [d1730, d6063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1730, d6063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1730, d6063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25393 (p : Pattern) (guard : d5540 p = 1) : d2910 p ≤ (2 : Int) + d6064 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2910, d6064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25371 p hg
    simpa only [d2910, d6064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2910, d6064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25392 p hg
    simpa only [d2910, d6064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25394 (p : Pattern) (guard : d5501 p = 1) : d1793 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25337 p hg
    simpa only [d5501, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24635 p hg
    simpa only [d5501, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25395 (p : Pattern) (guard : d0 p = 1) : d1796 p ≤ (2 : Int) + d1795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25396 (p : Pattern) (guard : d5540 p = 1) : d1797 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25394 p hg
    simpa only [d5540, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25395 p hg
    simpa only [d5540, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25397 (p : Pattern) (guard : d5540 p = 1) : d2911 p ≤ (2 : Int) + d6047 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2911, d6047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25336 p hg
    simpa only [d2911, d6047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2911, d6047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25396 p hg
    simpa only [d2911, d6047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25398 (p : Pattern) (guard : d5540 p = 1) : d2912 p ≤ (2 : Int) + d6065 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2912, d6065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25397 p hg
    simpa only [d2912, d6065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2912, d6065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2912, d6065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25399 (p : Pattern) (guard : d5540 p = 1) : d2913 p ≤ (2 : Int) + d6066 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2913, d6066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25393 p hg
    simpa only [d2913, d6066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2913, d6066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25398 p hg
    simpa only [d2913, d6066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25400 (p : Pattern) (guard : d5540 p = 1) : d2914 p ≤ (2 : Int) + d6067 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2914, d6067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25386 p hg
    simpa only [d2914, d6067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2914, d6067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25399 p hg
    simpa only [d2914, d6067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25401 (p : Pattern) (guard : d5540 p = 1) : d2915 p ≤ (2 : Int) + d6068 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2915, d6068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25371 p hg
    simpa only [d2915, d6068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2915, d6068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2915, d6068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25402 (p : Pattern) (guard : d5540 p = 1) : d2916 p ≤ (2 : Int) + d6069 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2916, d6069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25401 p hg
    simpa only [d2916, d6069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2916, d6069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25398 p hg
    simpa only [d2916, d6069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25403 (p : Pattern) (guard : d5540 p = 1) : d2917 p ≤ (2 : Int) + d6070 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2917, d6070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25357 p hg
    simpa only [d2917, d6070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2917, d6070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2917, d6070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25404 (p : Pattern) (guard : d5540 p = 1) : d2918 p ≤ (2 : Int) + d6071 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2918, d6071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25403 p hg
    simpa only [d2918, d6071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2918, d6071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2918, d6071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25405 (p : Pattern) (guard : d5540 p = 1) : d2919 p ≤ (2 : Int) + d6072 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2919, d6072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25402 p hg
    simpa only [d2919, d6072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2919, d6072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25404 p hg
    simpa only [d2919, d6072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25406 (p : Pattern) (guard : d5540 p = 1) : d2920 p ≤ (2 : Int) + d6073 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2920, d6073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25400 p hg
    simpa only [d2920, d6073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2920, d6073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25405 p hg
    simpa only [d2920, d6073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25407 (p : Pattern) (guard : d5540 p = 1) : d2921 p ≤ (2 : Int) + d6074 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2921, d6074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25367 p hg
    simpa only [d2921, d6074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2921, d6074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25406 p hg
    simpa only [d2921, d6074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25408 (p : Pattern) (guard : d5540 p = 1) : d31 p ≤ (2 : Int) + d31 p := by
  omega
theorem compare25409 (p : Pattern) (guard : d5501 p = 1) : d2029 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25372 p hg
    simpa only [d5501, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24691 p hg
    simpa only [d5501, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25410 (p : Pattern) (guard : d0 p = 1) : d1714 p ≤ (2 : Int) + d1714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25411 (p : Pattern) (guard : d5540 p = 1) : d2030 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25409 p hg
    simpa only [d5540, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25410 p hg
    simpa only [d5540, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25412 (p : Pattern) (guard : d5540 p = 1) : d2922 p ≤ (2 : Int) + d6075 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2922, d6075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25408 p hg
    simpa only [d2922, d6075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2922, d6075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25411 p hg
    simpa only [d2922, d6075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25413 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d1743 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25414 (p : Pattern) (guard : d1 p = 1) : d1743 p ≤ (2 : Int) + d1743 p := by
  omega
theorem compare25415 (p : Pattern) (guard : d5501 p = 1) : d1744 p ≤ (2 : Int) + d1743 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25413 p hg
    simpa only [d5501, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25414 p hg
    simpa only [d5501, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25416 (p : Pattern) (guard : d0 p = 1) : d1743 p ≤ (2 : Int) + d1743 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25417 (p : Pattern) (guard : d5540 p = 1) : d1745 p ≤ (2 : Int) + d1743 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25415 p hg
    simpa only [d5540, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25416 p hg
    simpa only [d5540, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25418 (p : Pattern) (guard : d5540 p = 1) : d1746 p ≤ (2 : Int) + d6076 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1746, d6076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25417 p hg
    simpa only [d1746, d6076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1746, d6076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1746, d6076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25419 (p : Pattern) (guard : d5540 p = 1) : d2923 p ≤ (2 : Int) + d6077 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2923, d6077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25412 p hg
    simpa only [d2923, d6077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2923, d6077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25418 p hg
    simpa only [d2923, d6077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25420 (p : Pattern) (guard : d5540 p = 1) : d2924 p ≤ (2 : Int) + d6078 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2924, d6078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25335 p hg
    simpa only [d2924, d6078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2924, d6078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25419 p hg
    simpa only [d2924, d6078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25421 (p : Pattern) (guard : d5540 p = 1) : d2925 p ≤ (2 : Int) + d6079 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2925, d6079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25348 p hg
    simpa only [d2925, d6079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2925, d6079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25364 p hg
    simpa only [d2925, d6079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25422 (p : Pattern) (guard : d5540 p = 1) : d2926 p ≤ (2 : Int) + d6080 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2926, d6080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25420 p hg
    simpa only [d2926, d6080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2926, d6080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25421 p hg
    simpa only [d2926, d6080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25423 (p : Pattern) (guard : d5540 p = 1) : d58 p ≤ (2 : Int) + d58 p := by
  omega
theorem compare25424 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (2 : Int) + d329 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25425 (p : Pattern) (guard : d1 p = 1) : d329 p ≤ (2 : Int) + d329 p := by
  omega
theorem compare25426 (p : Pattern) (guard : d5501 p = 1) : d1751 p ≤ (2 : Int) + d329 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25424 p hg
    simpa only [d5501, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25425 p hg
    simpa only [d5501, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25427 (p : Pattern) (guard : d0 p = 1) : d329 p ≤ (2 : Int) + d329 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25428 (p : Pattern) (guard : d5540 p = 1) : d1752 p ≤ (2 : Int) + d329 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25426 p hg
    simpa only [d5540, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25427 p hg
    simpa only [d5540, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25429 (p : Pattern) (guard : d5540 p = 1) : d2927 p ≤ (2 : Int) + d6081 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2927, d6081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25423 p hg
    simpa only [d2927, d6081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2927, d6081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25428 p hg
    simpa only [d2927, d6081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25430 (p : Pattern) (guard : d5540 p = 1) : d1753 p ≤ (2 : Int) + d6082 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1753, d6082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25428 p hg
    simpa only [d1753, d6082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1753, d6082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1753, d6082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25431 (p : Pattern) (guard : d5540 p = 1) : d2928 p ≤ (2 : Int) + d6083 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2928, d6083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25429 p hg
    simpa only [d2928, d6083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2928, d6083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25430 p hg
    simpa only [d2928, d6083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25432 (p : Pattern) (guard : d5540 p = 1) : d2929 p ≤ (2 : Int) + d6084 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2929, d6084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25348 p hg
    simpa only [d2929, d6084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2929, d6084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25431 p hg
    simpa only [d2929, d6084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25433 (p : Pattern) (guard : d5540 p = 1) : d40 p ≤ (2 : Int) + d40 p := by
  omega
theorem compare25434 (p : Pattern) (guard : d5540 p = 1) : d2930 p ≤ (2 : Int) + d6085 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2930, d6085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25433 p hg
    simpa only [d2930, d6085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2930, d6085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25391 p hg
    simpa only [d2930, d6085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25435 (p : Pattern) (guard : d5540 p = 1) : d2931 p ≤ (2 : Int) + d6086 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2931, d6086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25434 p hg
    simpa only [d2931, d6086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2931, d6086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25392 p hg
    simpa only [d2931, d6086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25436 (p : Pattern) (guard : d5540 p = 1) : d2932 p ≤ (2 : Int) + d6087 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2932, d6087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25435 p hg
    simpa only [d2932, d6087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2932, d6087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2932, d6087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25437 (p : Pattern) (guard : d5540 p = 1) : d2933 p ≤ (2 : Int) + d6088 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2933, d6088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25432 p hg
    simpa only [d2933, d6088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2933, d6088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25436 p hg
    simpa only [d2933, d6088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25438 (p : Pattern) (guard : d5540 p = 1) : d2934 p ≤ (2 : Int) + d6089 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2934, d6089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25422 p hg
    simpa only [d2934, d6089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2934, d6089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25437 p hg
    simpa only [d2934, d6089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25439 (p : Pattern) (guard : d5540 p = 1) : d2935 p ≤ (2 : Int) + d6075 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2935, d6075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25408 p hg
    simpa only [d2935, d6075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2935, d6075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25375 p hg
    simpa only [d2935, d6075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25440 (p : Pattern) (guard : d5540 p = 1) : d2936 p ≤ (2 : Int) + d6090 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2936, d6090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25439 p hg
    simpa only [d2936, d6090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2936, d6090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2936, d6090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25441 (p : Pattern) (guard : d5540 p = 1) : d2937 p ≤ (2 : Int) + d6091 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2937, d6091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25385 p hg
    simpa only [d2937, d6091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2937, d6091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25440 p hg
    simpa only [d2937, d6091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25442 (p : Pattern) (guard : d5540 p = 1) : d2938 p ≤ (2 : Int) + d6092 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2938, d6092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25398 p hg
    simpa only [d2938, d6092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2938, d6092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25403 p hg
    simpa only [d2938, d6092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25443 (p : Pattern) (guard : d5540 p = 1) : d2939 p ≤ (2 : Int) + d6093 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2939, d6093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25441 p hg
    simpa only [d2939, d6093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2939, d6093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25442 p hg
    simpa only [d2939, d6093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25444 (p : Pattern) (guard : d5540 p = 1) : d2940 p ≤ (2 : Int) + d6094 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2940, d6094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25429 p hg
    simpa only [d2940, d6094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2940, d6094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2940, d6094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25445 (p : Pattern) (guard : d5540 p = 1) : d2941 p ≤ (2 : Int) + d6095 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2941, d6095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25398 p hg
    simpa only [d2941, d6095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2941, d6095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25444 p hg
    simpa only [d2941, d6095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25446 (p : Pattern) (guard : d5540 p = 1) : d2942 p ≤ (2 : Int) + d6096 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2942, d6096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25434 p hg
    simpa only [d2942, d6096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2942, d6096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2942, d6096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25447 (p : Pattern) (guard : d5540 p = 1) : d2943 p ≤ (2 : Int) + d6097 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2943, d6097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25446 p hg
    simpa only [d2943, d6097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2943, d6097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2943, d6097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25448 (p : Pattern) (guard : d5540 p = 1) : d2944 p ≤ (2 : Int) + d6098 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2944, d6098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25445 p hg
    simpa only [d2944, d6098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2944, d6098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25447 p hg
    simpa only [d2944, d6098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25449 (p : Pattern) (guard : d5540 p = 1) : d2945 p ≤ (2 : Int) + d6099 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2945, d6099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25443 p hg
    simpa only [d2945, d6099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2945, d6099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25448 p hg
    simpa only [d2945, d6099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25450 (p : Pattern) (guard : d5540 p = 1) : d2946 p ≤ (2 : Int) + d6100 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2946, d6100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25438 p hg
    simpa only [d2946, d6100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2946, d6100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25449 p hg
    simpa only [d2946, d6100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25451 (p : Pattern) (guard : d5540 p = 1) : d2947 p ≤ (2 : Int) + d6101 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2947, d6101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25407 p hg
    simpa only [d2947, d6101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2947, d6101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25450 p hg
    simpa only [d2947, d6101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25452 (p : Pattern) (guard : d0 p = 1) : d2047 p ≤ (2 : Int) + d1770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25453 (p : Pattern) (guard : d5540 p = 1) : d2048 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25368 p hg
    simpa only [d5540, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25452 p hg
    simpa only [d5540, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25454 (p : Pattern) (guard : d5540 p = 1) : d2948 p ≤ (2 : Int) + d6044 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2948, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25322 p hg
    simpa only [d2948, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2948, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25453 p hg
    simpa only [d2948, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25455 (p : Pattern) (guard : d5540 p = 1) : d1773 p ≤ (2 : Int) + d6102 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1773, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25326 p hg
    simpa only [d1773, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1773, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1773, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25456 (p : Pattern) (guard : d5540 p = 1) : d2949 p ≤ (2 : Int) + d6103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2949, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25454 p hg
    simpa only [d2949, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2949, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25455 p hg
    simpa only [d2949, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25457 (p : Pattern) (guard : d0 p = 1) : d2053 p ≤ (2 : Int) + d1770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25458 (p : Pattern) (guard : d5540 p = 1) : d2054 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25368 p hg
    simpa only [d5540, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d5540, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25459 (p : Pattern) (guard : d5540 p = 1) : d2950 p ≤ (2 : Int) + d6044 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2950, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25322 p hg
    simpa only [d2950, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2950, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d2950, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25460 (p : Pattern) (guard : d0 p = 1) : d1780 p ≤ (2 : Int) + d1770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25461 (p : Pattern) (guard : d5540 p = 1) : d1781 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25368 p hg
    simpa only [d5540, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d5540, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25462 (p : Pattern) (guard : d5540 p = 1) : d1782 p ≤ (2 : Int) + d6102 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1782, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d1782, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1782, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1782, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25463 (p : Pattern) (guard : d5540 p = 1) : d2951 p ≤ (2 : Int) + d6103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2951, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d2951, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2951, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d2951, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25464 (p : Pattern) (guard : d5540 p = 1) : d2952 p ≤ (2 : Int) + d6103 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25465 (p : Pattern) (guard : d5540 p = 1) : d1789 p ≤ (2 : Int) + d6102 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1789, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25370 p hg
    simpa only [d1789, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1789, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1789, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25466 (p : Pattern) (guard : d5540 p = 1) : d2953 p ≤ (2 : Int) + d6103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2953, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25371 p hg
    simpa only [d2953, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2953, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25465 p hg
    simpa only [d2953, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25467 (p : Pattern) (guard : d5540 p = 1) : d1798 p ≤ (2 : Int) + d6104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1798, d6104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25396 p hg
    simpa only [d1798, d6104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1798, d6104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1798, d6104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25468 (p : Pattern) (guard : d5540 p = 1) : d2954 p ≤ (2 : Int) + d6105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2954, d6105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25397 p hg
    simpa only [d2954, d6105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2954, d6105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25467 p hg
    simpa only [d2954, d6105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25469 (p : Pattern) (guard : d5540 p = 1) : d2955 p ≤ (2 : Int) + d6106 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2955, d6106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25466 p hg
    simpa only [d2955, d6106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2955, d6106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2955, d6106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25470 (p : Pattern) (guard : d5540 p = 1) : d2956 p ≤ (2 : Int) + d6107 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2956, d6107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d2956, d6107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2956, d6107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25469 p hg
    simpa only [d2956, d6107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25471 (p : Pattern) (guard : d5540 p = 1) : d1804 p ≤ (2 : Int) + d6108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1804, d6108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25356 p hg
    simpa only [d1804, d6108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1804, d6108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1804, d6108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25472 (p : Pattern) (guard : d5540 p = 1) : d2957 p ≤ (2 : Int) + d6109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2957, d6109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25357 p hg
    simpa only [d2957, d6109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2957, d6109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25471 p hg
    simpa only [d2957, d6109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25473 (p : Pattern) (guard : d5540 p = 1) : d2958 p ≤ (2 : Int) + d6110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2958, d6110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25472 p hg
    simpa only [d2958, d6110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2958, d6110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2958, d6110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25474 (p : Pattern) (guard : d5540 p = 1) : d2959 p ≤ (2 : Int) + d6111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2959, d6111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25469 p hg
    simpa only [d2959, d6111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2959, d6111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25473 p hg
    simpa only [d2959, d6111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25475 (p : Pattern) (guard : d5540 p = 1) : d2960 p ≤ (2 : Int) + d6112 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2960, d6112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25470 p hg
    simpa only [d2960, d6112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2960, d6112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25474 p hg
    simpa only [d2960, d6112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25476 (p : Pattern) (guard : d5540 p = 1) : d2961 p ≤ (2 : Int) + d6113 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2961, d6113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25439 p hg
    simpa only [d2961, d6113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2961, d6113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25376 p hg
    simpa only [d2961, d6113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25477 (p : Pattern) (guard : d5540 p = 1) : d35 p ≤ (2 : Int) + d35 p := by
  omega
theorem compare25478 (p : Pattern) (guard : d5540 p = 1) : d2962 p ≤ (2 : Int) + d6114 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2962, d6114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25477 p hg
    simpa only [d2962, d6114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2962, d6114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25383 p hg
    simpa only [d2962, d6114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25479 (p : Pattern) (guard : d5540 p = 1) : d2963 p ≤ (2 : Int) + d6115 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2963, d6115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d2963, d6115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2963, d6115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25384 p hg
    simpa only [d2963, d6115, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
