/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons238
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33460 (p : Pattern) (guard : d5843 p = 1) : d1939 p ≤ (2 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33459 p hg
    simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33461 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33462 (p : Pattern) (guard : d5843 p = 1) : d1940 p ≤ (2 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1940, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33460 p hg
    simpa only [d1940, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1940, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33461 p hg
    simpa only [d1940, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33463 (p : Pattern) (guard : d5843 p = 1) : d1941 p ≤ (2 : Int) + d7806 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1941, d7806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d1941, d7806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1941, d7806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33462 p hg
    simpa only [d1941, d7806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33464 (p : Pattern) (guard : d5843 p = 1) : d1942 p ≤ (2 : Int) + d7807 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1942, d7807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33463 p hg
    simpa only [d1942, d7807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1942, d7807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33462 p hg
    simpa only [d1942, d7807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33465 (p : Pattern) (guard : d5843 p = 1) : d2993 p ≤ (2 : Int) + d7808 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2993, d7808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d2993, d7808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2993, d7808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33464 p hg
    simpa only [d2993, d7808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33466 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33467 (p : Pattern) (guard : d5843 p = 1) : d1872 p ≤ (2 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14090 p hg
    simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33466 p hg
    simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33468 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33469 (p : Pattern) (guard : d5843 p = 1) : d1873 p ≤ (2 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1873, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33467 p hg
    simpa only [d1873, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1873, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33468 p hg
    simpa only [d1873, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33470 (p : Pattern) (guard : d5843 p = 1) : d1874 p ≤ (2 : Int) + d7809 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1874, d7809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d1874, d7809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1874, d7809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33469 p hg
    simpa only [d1874, d7809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33471 (p : Pattern) (guard : d5843 p = 1) : d1875 p ≤ (2 : Int) + d7810 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1875, d7810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33470 p hg
    simpa only [d1875, d7810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1875, d7810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33469 p hg
    simpa only [d1875, d7810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33472 (p : Pattern) (guard : d5843 p = 1) : d1876 p ≤ (2 : Int) + d7811 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1876, d7811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33471 p hg
    simpa only [d1876, d7811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1876, d7811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1876, d7811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33473 (p : Pattern) (guard : d5843 p = 1) : d2994 p ≤ (2 : Int) + d7812 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2994, d7812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33465 p hg
    simpa only [d2994, d7812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2994, d7812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33472 p hg
    simpa only [d2994, d7812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33474 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (2 : Int) + d5 p := by
  omega
theorem compare33475 (p : Pattern) (guard : d5843 p = 1) : d107 p ≤ (2 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33474 p hg
    simpa only [d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33461 p hg
    simpa only [d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33476 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33477 (p : Pattern) (guard : d5843 p = 1) : d1963 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16235 p hg
    simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33476 p hg
    simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33478 (p : Pattern) (guard : d5843 p = 1) : d1964 p ≤ (2 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1964, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33477 p hg
    simpa only [d1964, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1964, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33283 p hg
    simpa only [d1964, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33479 (p : Pattern) (guard : d5843 p = 1) : d2129 p ≤ (2 : Int) + d7813 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2129, d7813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33475 p hg
    simpa only [d2129, d7813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2129, d7813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33478 p hg
    simpa only [d2129, d7813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33480 (p : Pattern) (guard : d5843 p = 1) : d2130 p ≤ (2 : Int) + d7814 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2130, d7814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33479 p hg
    simpa only [d2130, d7814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2130, d7814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33478 p hg
    simpa only [d2130, d7814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33481 (p : Pattern) (guard : d5843 p = 1) : d2995 p ≤ (2 : Int) + d7815 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2995, d7815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33475 p hg
    simpa only [d2995, d7815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2995, d7815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33480 p hg
    simpa only [d2995, d7815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33482 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33483 (p : Pattern) (guard : d5843 p = 1) : d1880 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33482 p hg
    simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33484 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33485 (p : Pattern) (guard : d5843 p = 1) : d1881 p ≤ (2 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1881, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33483 p hg
    simpa only [d1881, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1881, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33484 p hg
    simpa only [d1881, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33486 (p : Pattern) (guard : d5843 p = 1) : d1882 p ≤ (2 : Int) + d7816 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1882, d7816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33475 p hg
    simpa only [d1882, d7816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1882, d7816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33485 p hg
    simpa only [d1882, d7816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33487 (p : Pattern) (guard : d5843 p = 1) : d1883 p ≤ (2 : Int) + d7817 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1883, d7817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33486 p hg
    simpa only [d1883, d7817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1883, d7817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33485 p hg
    simpa only [d1883, d7817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33488 (p : Pattern) (guard : d5843 p = 1) : d1884 p ≤ (2 : Int) + d7818 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1884, d7818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33487 p hg
    simpa only [d1884, d7818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1884, d7818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1884, d7818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33489 (p : Pattern) (guard : d5843 p = 1) : d2996 p ≤ (2 : Int) + d7819 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2996, d7819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33481 p hg
    simpa only [d2996, d7819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2996, d7819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33488 p hg
    simpa only [d2996, d7819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33490 (p : Pattern) (guard : d5843 p = 1) : d2997 p ≤ (2 : Int) + d7820 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2997, d7820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33473 p hg
    simpa only [d2997, d7820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2997, d7820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33489 p hg
    simpa only [d2997, d7820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33491 (p : Pattern) (guard : d5843 p = 1) : d2998 p ≤ (2 : Int) + d7821 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2998, d7821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33473 p hg
    simpa only [d2998, d7821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2998, d7821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33490 p hg
    simpa only [d2998, d7821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33492 (p : Pattern) (guard : d5843 p = 1) : d2999 p ≤ (2 : Int) + d7822 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2999, d7822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33376 p hg
    simpa only [d2999, d7822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2999, d7822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2999, d7822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33493 (p : Pattern) (guard : d5843 p = 1) : d3000 p ≤ (2 : Int) + d7823 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3000, d7823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33490 p hg
    simpa only [d3000, d7823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3000, d7823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33492 p hg
    simpa only [d3000, d7823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33494 (p : Pattern) (guard : d5843 p = 1) : d3001 p ≤ (2 : Int) + d7824 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3001, d7824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33491 p hg
    simpa only [d3001, d7824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3001, d7824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33493 p hg
    simpa only [d3001, d7824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33495 (p : Pattern) (guard : d5843 p = 1) : d1945 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d5843, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33482 p hg
    simpa only [d5843, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33496 (p : Pattern) (guard : d5843 p = 1) : d1946 p ≤ (2 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1946, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33495 p hg
    simpa only [d1946, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1946, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33484 p hg
    simpa only [d1946, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33497 (p : Pattern) (guard : d5843 p = 1) : d1947 p ≤ (2 : Int) + d7825 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1947, d7825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d1947, d7825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1947, d7825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33496 p hg
    simpa only [d1947, d7825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33498 (p : Pattern) (guard : d5843 p = 1) : d1955 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33457 p hg
    simpa only [d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33326 p hg
    simpa only [d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33499 (p : Pattern) (guard : d5843 p = 1) : d1956 p ≤ (2 : Int) + d7826 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1956, d7826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33462 p hg
    simpa only [d1956, d7826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1956, d7826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33498 p hg
    simpa only [d1956, d7826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33500 (p : Pattern) (guard : d5843 p = 1) : d1957 p ≤ (2 : Int) + d7827 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1957, d7827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33497 p hg
    simpa only [d1957, d7827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1957, d7827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33499 p hg
    simpa only [d1957, d7827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33501 (p : Pattern) (guard : d5843 p = 1) : d3002 p ≤ (2 : Int) + d7828 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3002, d7828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d3002, d7828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3002, d7828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33500 p hg
    simpa only [d3002, d7828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33502 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (2 : Int) + d3 p := by
  omega
theorem compare33503 (p : Pattern) (guard : d5843 p = 1) : d116 p ≤ (2 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33502 p hg
    simpa only [d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33468 p hg
    simpa only [d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33504 (p : Pattern) (guard : d5843 p = 1) : d1891 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16260 p hg
    simpa only [d5843, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33476 p hg
    simpa only [d5843, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33505 (p : Pattern) (guard : d5843 p = 1) : d1892 p ≤ (2 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1892, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33504 p hg
    simpa only [d1892, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1892, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33283 p hg
    simpa only [d1892, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33506 (p : Pattern) (guard : d5843 p = 1) : d1893 p ≤ (2 : Int) + d7829 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1893, d7829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33503 p hg
    simpa only [d1893, d7829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1893, d7829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33505 p hg
    simpa only [d1893, d7829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33507 (p : Pattern) (guard : d5843 p = 1) : d1894 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24795 p hg
    simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33482 p hg
    simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33508 (p : Pattern) (guard : d5843 p = 1) : d1895 p ≤ (2 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1895, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33507 p hg
    simpa only [d1895, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1895, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33484 p hg
    simpa only [d1895, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33509 (p : Pattern) (guard : d5843 p = 1) : d1896 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33468 p hg
    simpa only [d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33510 (p : Pattern) (guard : d5843 p = 1) : d1897 p ≤ (2 : Int) + d7830 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1897, d7830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33508 p hg
    simpa only [d1897, d7830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1897, d7830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33509 p hg
    simpa only [d1897, d7830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33511 (p : Pattern) (guard : d5843 p = 1) : d1898 p ≤ (2 : Int) + d7831 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1898, d7831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33506 p hg
    simpa only [d1898, d7831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1898, d7831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33510 p hg
    simpa only [d1898, d7831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33512 (p : Pattern) (guard : d5843 p = 1) : d1899 p ≤ (2 : Int) + d7832 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1899, d7832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33511 p hg
    simpa only [d1899, d7832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1899, d7832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1899, d7832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33513 (p : Pattern) (guard : d5843 p = 1) : d3003 p ≤ (2 : Int) + d7833 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3003, d7833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33501 p hg
    simpa only [d3003, d7833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3003, d7833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33512 p hg
    simpa only [d3003, d7833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33514 (p : Pattern) (guard : d5843 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  omega
theorem compare33515 (p : Pattern) (guard : d5843 p = 1) : d120 p ≤ (2 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33514 p hg
    simpa only [d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33484 p hg
    simpa only [d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33516 (p : Pattern) (guard : d5843 p = 1) : d317 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33484 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33517 (p : Pattern) (guard : d5843 p = 1) : d1901 p ≤ (2 : Int) + d7830 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1901, d7830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33515 p hg
    simpa only [d1901, d7830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1901, d7830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33516 p hg
    simpa only [d1901, d7830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33518 (p : Pattern) (guard : d5843 p = 1) : d1902 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16298 p hg
    simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33289 p hg
    simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33519 (p : Pattern) (guard : d5843 p = 1) : d1903 p ≤ (2 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1903, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33518 p hg
    simpa only [d1903, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1903, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d1903, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33520 (p : Pattern) (guard : d5843 p = 1) : d1904 p ≤ (2 : Int) + d7702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1904, d7702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33519 p hg
    simpa only [d1904, d7702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1904, d7702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33516 p hg
    simpa only [d1904, d7702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33521 (p : Pattern) (guard : d5843 p = 1) : d1905 p ≤ (2 : Int) + d7834 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1905, d7834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33517 p hg
    simpa only [d1905, d7834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1905, d7834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33520 p hg
    simpa only [d1905, d7834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33522 (p : Pattern) (guard : d5843 p = 1) : d1906 p ≤ (2 : Int) + d7835 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1906, d7835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33521 p hg
    simpa only [d1906, d7835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1906, d7835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1906, d7835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33523 (p : Pattern) (guard : d5843 p = 1) : d3004 p ≤ (2 : Int) + d7836 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3004, d7836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33501 p hg
    simpa only [d3004, d7836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3004, d7836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33522 p hg
    simpa only [d3004, d7836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33524 (p : Pattern) (guard : d5843 p = 1) : d3005 p ≤ (2 : Int) + d7837 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3005, d7837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33513 p hg
    simpa only [d3005, d7837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3005, d7837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33523 p hg
    simpa only [d3005, d7837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33525 (p : Pattern) (guard : d5843 p = 1) : d3006 p ≤ (2 : Int) + d7838 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3006, d7838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33501 p hg
    simpa only [d3006, d7838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3006, d7838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3006, d7838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33526 (p : Pattern) (guard : d5843 p = 1) : d1960 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16303 p hg
    simpa only [d5843, d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33289 p hg
    simpa only [d5843, d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33527 (p : Pattern) (guard : d5843 p = 1) : d1961 p ≤ (2 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1961, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33526 p hg
    simpa only [d1961, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1961, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d1961, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33528 (p : Pattern) (guard : d5843 p = 1) : d1962 p ≤ (2 : Int) + d7839 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1962, d7839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33475 p hg
    simpa only [d1962, d7839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1962, d7839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33527 p hg
    simpa only [d1962, d7839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33529 (p : Pattern) (guard : d5843 p = 1) : d348 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33461 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33530 (p : Pattern) (guard : d5843 p = 1) : d1965 p ≤ (2 : Int) + d7678 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1965, d7678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33478 p hg
    simpa only [d1965, d7678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1965, d7678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33529 p hg
    simpa only [d1965, d7678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33531 (p : Pattern) (guard : d5843 p = 1) : d1966 p ≤ (2 : Int) + d7840 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1966, d7840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33528 p hg
    simpa only [d1966, d7840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1966, d7840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33530 p hg
    simpa only [d1966, d7840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33532 (p : Pattern) (guard : d5843 p = 1) : d3007 p ≤ (2 : Int) + d7841 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3007, d7841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33475 p hg
    simpa only [d3007, d7841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3007, d7841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33531 p hg
    simpa only [d3007, d7841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33533 (p : Pattern) (guard : d5843 p = 1) : d3008 p ≤ (2 : Int) + d7842 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3008, d7842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33532 p hg
    simpa only [d3008, d7842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3008, d7842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3008, d7842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33534 (p : Pattern) (guard : d5843 p = 1) : d3009 p ≤ (2 : Int) + d7843 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3009, d7843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33525 p hg
    simpa only [d3009, d7843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3009, d7843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33533 p hg
    simpa only [d3009, d7843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33535 (p : Pattern) (guard : d5843 p = 1) : d3010 p ≤ (2 : Int) + d7844 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3010, d7844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33524 p hg
    simpa only [d3010, d7844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3010, d7844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33534 p hg
    simpa only [d3010, d7844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33536 (p : Pattern) (guard : d5843 p = 1) : d3011 p ≤ (2 : Int) + d7845 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3011, d7845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33388 p hg
    simpa only [d3011, d7845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3011, d7845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3011, d7845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33537 (p : Pattern) (guard : d5843 p = 1) : d3012 p ≤ (2 : Int) + d7846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3012, d7846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33534 p hg
    simpa only [d3012, d7846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3012, d7846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33536 p hg
    simpa only [d3012, d7846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33538 (p : Pattern) (guard : d5843 p = 1) : d3013 p ≤ (2 : Int) + d7847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3013, d7847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33535 p hg
    simpa only [d3013, d7847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3013, d7847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33537 p hg
    simpa only [d3013, d7847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33539 (p : Pattern) (guard : d5843 p = 1) : d3014 p ≤ (2 : Int) + d7848 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3014, d7848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33494 p hg
    simpa only [d3014, d7848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3014, d7848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33538 p hg
    simpa only [d3014, d7848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33540 (p : Pattern) (guard : d5843 p = 1) : d2124 p ≤ (2 : Int) + d7849 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2124, d7849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33503 p hg
    simpa only [d2124, d7849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2124, d7849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33508 p hg
    simpa only [d2124, d7849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33541 (p : Pattern) (guard : d5843 p = 1) : d2125 p ≤ (2 : Int) + d7850 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2125, d7850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33540 p hg
    simpa only [d2125, d7850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2125, d7850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33508 p hg
    simpa only [d2125, d7850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33542 (p : Pattern) (guard : d5843 p = 1) : d3015 p ≤ (2 : Int) + d7851 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3015, d7851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33503 p hg
    simpa only [d3015, d7851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3015, d7851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33541 p hg
    simpa only [d3015, d7851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33543 (p : Pattern) (guard : d5843 p = 1) : d1918 p ≤ (2 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4913 p hg
    simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33459 p hg
    simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33544 (p : Pattern) (guard : d5843 p = 1) : d1919 p ≤ (2 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1919, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33543 p hg
    simpa only [d1919, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1919, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33461 p hg
    simpa only [d1919, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33545 (p : Pattern) (guard : d5843 p = 1) : d1920 p ≤ (2 : Int) + d7852 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1920, d7852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33503 p hg
    simpa only [d1920, d7852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1920, d7852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33544 p hg
    simpa only [d1920, d7852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33546 (p : Pattern) (guard : d5843 p = 1) : d1921 p ≤ (2 : Int) + d7853 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1921, d7853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33545 p hg
    simpa only [d1921, d7853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1921, d7853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33544 p hg
    simpa only [d1921, d7853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33547 (p : Pattern) (guard : d5843 p = 1) : d1922 p ≤ (2 : Int) + d7854 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1922, d7854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33546 p hg
    simpa only [d1922, d7854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1922, d7854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1922, d7854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33548 (p : Pattern) (guard : d5843 p = 1) : d3016 p ≤ (2 : Int) + d7855 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3016, d7855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33542 p hg
    simpa only [d3016, d7855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3016, d7855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33547 p hg
    simpa only [d3016, d7855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33549 (p : Pattern) (guard : d5843 p = 1) : d3017 p ≤ (2 : Int) + d7856 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3017, d7856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33473 p hg
    simpa only [d3017, d7856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3017, d7856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33548 p hg
    simpa only [d3017, d7856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33550 (p : Pattern) (guard : d5843 p = 1) : d3018 p ≤ (2 : Int) + d7857 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3018, d7857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33489 p hg
    simpa only [d3018, d7857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3018, d7857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33376 p hg
    simpa only [d3018, d7857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33551 (p : Pattern) (guard : d5843 p = 1) : d3019 p ≤ (2 : Int) + d7858 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3019, d7858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33549 p hg
    simpa only [d3019, d7858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3019, d7858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33550 p hg
    simpa only [d3019, d7858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33552 (p : Pattern) (guard : d5843 p = 1) : d3020 p ≤ (2 : Int) + d7859 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3020, d7859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33489 p hg
    simpa only [d3020, d7859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3020, d7859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d3020, d7859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33553 (p : Pattern) (guard : d5843 p = 1) : d3021 p ≤ (2 : Int) + d7860 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3021, d7860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33552 p hg
    simpa only [d3021, d7860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3021, d7860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3021, d7860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33554 (p : Pattern) (guard : d5843 p = 1) : d3022 p ≤ (2 : Int) + d7861 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3022, d7861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33551 p hg
    simpa only [d3022, d7861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3022, d7861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33553 p hg
    simpa only [d3022, d7861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33555 (p : Pattern) (guard : d5843 p = 1) : d3023 p ≤ (2 : Int) + d7862 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3023, d7862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33503 p hg
    simpa only [d3023, d7862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3023, d7862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33511 p hg
    simpa only [d3023, d7862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33556 (p : Pattern) (guard : d5843 p = 1) : d3024 p ≤ (2 : Int) + d7863 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3024, d7863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33555 p hg
    simpa only [d3024, d7863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3024, d7863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3024, d7863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33557 (p : Pattern) (guard : d5843 p = 1) : d3025 p ≤ (2 : Int) + d7864 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3025, d7864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33523 p hg
    simpa only [d3025, d7864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3025, d7864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33556 p hg
    simpa only [d3025, d7864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33558 (p : Pattern) (guard : d5843 p = 1) : d3026 p ≤ (2 : Int) + d7865 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3026, d7865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33533 p hg
    simpa only [d3026, d7865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3026, d7865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33388 p hg
    simpa only [d3026, d7865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33559 (p : Pattern) (guard : d5843 p = 1) : d3027 p ≤ (2 : Int) + d7866 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3027, d7866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33557 p hg
    simpa only [d3027, d7866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3027, d7866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33558 p hg
    simpa only [d3027, d7866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33560 (p : Pattern) (guard : d5843 p = 1) : d3028 p ≤ (2 : Int) + d7867 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3028, d7867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33533 p hg
    simpa only [d3028, d7867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3028, d7867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33390 p hg
    simpa only [d3028, d7867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33561 (p : Pattern) (guard : d5843 p = 1) : d3029 p ≤ (2 : Int) + d7868 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3029, d7868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33560 p hg
    simpa only [d3029, d7868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3029, d7868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3029, d7868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33562 (p : Pattern) (guard : d5843 p = 1) : d3030 p ≤ (2 : Int) + d7869 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3030, d7869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33559 p hg
    simpa only [d3030, d7869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3030, d7869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33561 p hg
    simpa only [d3030, d7869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33563 (p : Pattern) (guard : d5843 p = 1) : d3031 p ≤ (2 : Int) + d7870 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3031, d7870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33554 p hg
    simpa only [d3031, d7870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3031, d7870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33562 p hg
    simpa only [d3031, d7870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33564 (p : Pattern) (guard : d5843 p = 1) : d3032 p ≤ (2 : Int) + d7871 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3032, d7871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33539 p hg
    simpa only [d3032, d7871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3032, d7871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33563 p hg
    simpa only [d3032, d7871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33565 (p : Pattern) (guard : d5843 p = 1) : d2107 p ≤ (2 : Int) + d7816 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2107, d7816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33462 p hg
    simpa only [d2107, d7816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2107, d7816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33496 p hg
    simpa only [d2107, d7816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33566 (p : Pattern) (guard : d5843 p = 1) : d2108 p ≤ (2 : Int) + d7872 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2108, d7872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33497 p hg
    simpa only [d2108, d7872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2108, d7872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33565 p hg
    simpa only [d2108, d7872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33567 (p : Pattern) (guard : d5843 p = 1) : d3033 p ≤ (2 : Int) + d7873 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3033, d7873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d3033, d7873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3033, d7873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33566 p hg
    simpa only [d3033, d7873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33568 (p : Pattern) (guard : d5843 p = 1) : d1943 p ≤ (2 : Int) + d7874 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1943, d7874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33464 p hg
    simpa only [d1943, d7874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1943, d7874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1943, d7874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33569 (p : Pattern) (guard : d5843 p = 1) : d3034 p ≤ (2 : Int) + d7875 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3034, d7875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33567 p hg
    simpa only [d3034, d7875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3034, d7875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33568 p hg
    simpa only [d3034, d7875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33570 (p : Pattern) (guard : d5843 p = 1) : d3035 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16295 p hg
    simpa only [d5843, d3035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33289 p hg
    simpa only [d5843, d3035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33571 (p : Pattern) (guard : d5843 p = 1) : d3036 p ≤ (2 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3036, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33570 p hg
    simpa only [d3036, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3036, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33326 p hg
    simpa only [d3036, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33572 (p : Pattern) (guard : d5843 p = 1) : d3037 p ≤ (2 : Int) + d7839 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3037, d7839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33462 p hg
    simpa only [d3037, d7839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3037, d7839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33571 p hg
    simpa only [d3037, d7839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33573 (p : Pattern) (guard : d5843 p = 1) : d3038 p ≤ (2 : Int) + d7876 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3038, d7876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33497 p hg
    simpa only [d3038, d7876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3038, d7876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33572 p hg
    simpa only [d3038, d7876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33574 (p : Pattern) (guard : d5843 p = 1) : d3039 p ≤ (2 : Int) + d7877 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3039, d7877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d3039, d7877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3039, d7877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33573 p hg
    simpa only [d3039, d7877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33575 (p : Pattern) (guard : d5843 p = 1) : d1948 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32563 p hg
    simpa only [d5843, d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33476 p hg
    simpa only [d5843, d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33576 (p : Pattern) (guard : d5843 p = 1) : d1949 p ≤ (2 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1949, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33575 p hg
    simpa only [d1949, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1949, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33283 p hg
    simpa only [d1949, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33577 (p : Pattern) (guard : d5843 p = 1) : d1950 p ≤ (2 : Int) + d7813 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1950, d7813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33462 p hg
    simpa only [d1950, d7813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1950, d7813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33576 p hg
    simpa only [d1950, d7813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33578 (p : Pattern) (guard : d5843 p = 1) : d1951 p ≤ (2 : Int) + d7878 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1951, d7878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33497 p hg
    simpa only [d1951, d7878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1951, d7878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33577 p hg
    simpa only [d1951, d7878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33579 (p : Pattern) (guard : d5843 p = 1) : d1952 p ≤ (2 : Int) + d7879 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1952, d7879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33578 p hg
    simpa only [d1952, d7879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1952, d7879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1952, d7879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33580 (p : Pattern) (guard : d5843 p = 1) : d3040 p ≤ (2 : Int) + d7880 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3040, d7880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33574 p hg
    simpa only [d3040, d7880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3040, d7880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33579 p hg
    simpa only [d3040, d7880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33581 (p : Pattern) (guard : d5843 p = 1) : d3041 p ≤ (2 : Int) + d7881 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3041, d7881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33569 p hg
    simpa only [d3041, d7881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3041, d7881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33580 p hg
    simpa only [d3041, d7881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33582 (p : Pattern) (guard : d5843 p = 1) : d1958 p ≤ (2 : Int) + d7882 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1958, d7882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33500 p hg
    simpa only [d1958, d7882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1958, d7882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1958, d7882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33583 (p : Pattern) (guard : d5843 p = 1) : d3042 p ≤ (2 : Int) + d7883 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3042, d7883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33501 p hg
    simpa only [d3042, d7883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3042, d7883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33582 p hg
    simpa only [d3042, d7883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33584 (p : Pattern) (guard : d5843 p = 1) : d1967 p ≤ (2 : Int) + d7884 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1967, d7884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33531 p hg
    simpa only [d1967, d7884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1967, d7884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1967, d7884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33585 (p : Pattern) (guard : d5843 p = 1) : d3043 p ≤ (2 : Int) + d7885 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3043, d7885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33532 p hg
    simpa only [d3043, d7885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3043, d7885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33584 p hg
    simpa only [d3043, d7885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33586 (p : Pattern) (guard : d5843 p = 1) : d3044 p ≤ (2 : Int) + d7886 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3044, d7886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33583 p hg
    simpa only [d3044, d7886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3044, d7886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33585 p hg
    simpa only [d3044, d7886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33587 (p : Pattern) (guard : d5843 p = 1) : d3045 p ≤ (2 : Int) + d7887 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3045, d7887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33581 p hg
    simpa only [d3045, d7887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3045, d7887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33586 p hg
    simpa only [d3045, d7887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33588 (p : Pattern) (guard : d5843 p = 1) : d3046 p ≤ (2 : Int) + d7888 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3046, d7888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33586 p hg
    simpa only [d3046, d7888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3046, d7888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33492 p hg
    simpa only [d3046, d7888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33589 (p : Pattern) (guard : d5843 p = 1) : d3047 p ≤ (2 : Int) + d7889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3047, d7889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33587 p hg
    simpa only [d3047, d7889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3047, d7889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33588 p hg
    simpa only [d3047, d7889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33590 (p : Pattern) (guard : d5843 p = 1) : d3048 p ≤ (2 : Int) + d7890 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3048, d7890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33555 p hg
    simpa only [d3048, d7890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3048, d7890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33512 p hg
    simpa only [d3048, d7890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33591 (p : Pattern) (guard : d5843 p = 1) : d3049 p ≤ (2 : Int) + d7891 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3049, d7891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33515 p hg
    simpa only [d3049, d7891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3049, d7891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33521 p hg
    simpa only [d3049, d7891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33592 (p : Pattern) (guard : d5843 p = 1) : d3050 p ≤ (2 : Int) + d7892 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3050, d7892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33591 p hg
    simpa only [d3050, d7892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3050, d7892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33522 p hg
    simpa only [d3050, d7892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33593 (p : Pattern) (guard : d5843 p = 1) : d3051 p ≤ (2 : Int) + d7893 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3051, d7893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33590 p hg
    simpa only [d3051, d7893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3051, d7893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33592 p hg
    simpa only [d3051, d7893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33594 (p : Pattern) (guard : d5843 p = 1) : d3052 p ≤ (2 : Int) + d7894 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3052, d7894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33593 p hg
    simpa only [d3052, d7894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3052, d7894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3052, d7894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33595 (p : Pattern) (guard : d5843 p = 1) : d3053 p ≤ (2 : Int) + d7895 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3053, d7895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33594 p hg
    simpa only [d3053, d7895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3053, d7895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3053, d7895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33596 (p : Pattern) (guard : d5843 p = 1) : d3054 p ≤ (2 : Int) + d7896 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3054, d7896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33589 p hg
    simpa only [d3054, d7896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3054, d7896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33595 p hg
    simpa only [d3054, d7896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33597 (p : Pattern) (guard : d5843 p = 1) : d3055 p ≤ (2 : Int) + d7897 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3055, d7897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33580 p hg
    simpa only [d3055, d7897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3055, d7897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33590 p hg
    simpa only [d3055, d7897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33598 (p : Pattern) (guard : d5843 p = 1) : d3056 p ≤ (2 : Int) + d7898 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3056, d7898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33585 p hg
    simpa only [d3056, d7898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3056, d7898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33376 p hg
    simpa only [d3056, d7898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33599 (p : Pattern) (guard : d5843 p = 1) : d3057 p ≤ (2 : Int) + d7899 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3057, d7899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33597 p hg
    simpa only [d3057, d7899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3057, d7899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33598 p hg
    simpa only [d3057, d7899, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
