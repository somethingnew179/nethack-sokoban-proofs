/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons124
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17500 (p : Pattern) (guard : d5537 p = 1) : d2049 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2049, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17499 p hg
    simpa only [d5537, d2049, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2049, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2049, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17501 (p : Pattern) (guard : d5537 p = 1) : d2050 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2050, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d2050, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2050, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17500 p hg
    simpa only [d2050, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17502 (p : Pattern) (guard : d0 p = 1) : d2052 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17503 (p : Pattern) (guard : d5502 p = 1) : d2053 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2053, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d2053, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2053, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17502 p hg
    simpa only [d5502, d2053, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17504 (p : Pattern) (guard : d5502 p = 1) : d2054 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2054, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17208 p hg
    simpa only [d2054, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2054, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17503 p hg
    simpa only [d2054, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17505 (p : Pattern) (guard : d5537 p = 1) : d2055 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2055, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17504 p hg
    simpa only [d5537, d2055, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2055, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2055, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17506 (p : Pattern) (guard : d5537 p = 1) : d2056 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2056, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d2056, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2056, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17505 p hg
    simpa only [d2056, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17507 (p : Pattern) (guard : d5537 p = 1) : d2057 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17501 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17506 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17508 (p : Pattern) (guard : d5537 p = 1) : d2058 p ≤ (0 : Int) + d2810 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2058, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17507 p hg
    simpa only [d2058, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2058, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17244 p hg
    simpa only [d2058, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17509 (p : Pattern) (guard : d5537 p = 1) : d2059 p ≤ (0 : Int) + d2811 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2059, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17508 p hg
    simpa only [d2059, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2059, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17245 p hg
    simpa only [d2059, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17510 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2813 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17511 (p : Pattern) (guard : d5537 p = 1) : d192 p ≤ (0 : Int) + d2814 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d192, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15172 p hg
    simpa only [d5537, d192, d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d192, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17510 p hg
    simpa only [d5537, d192, d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17512 (p : Pattern) (guard : d0 p = 1) : d315 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17513 (p : Pattern) (guard : d5502 p = 1) : d2060 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2060, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d5502, d2060, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2060, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17512 p hg
    simpa only [d5502, d2060, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17514 (p : Pattern) (guard : d1 p = 1) : d315 p ≤ (0 : Int) + d315 p := by
  omega
theorem compare17515 (p : Pattern) (guard : d5502 p = 1) : d315 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17514 p hg
    simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17512 p hg
    simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17516 (p : Pattern) (guard : d5502 p = 1) : d2061 p ≤ (0 : Int) + d2813 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2061, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17513 p hg
    simpa only [d2061, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2061, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17515 p hg
    simpa only [d2061, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17517 (p : Pattern) (guard : d5537 p = 1) : d2062 p ≤ (0 : Int) + d2815 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2062, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17516 p hg
    simpa only [d5537, d2062, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2062, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2062, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17518 (p : Pattern) (guard : d5537 p = 1) : d2063 p ≤ (0 : Int) + d2816 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2063, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17511 p hg
    simpa only [d2063, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2063, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17517 p hg
    simpa only [d2063, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17519 (p : Pattern) (guard : d5537 p = 1) : d2064 p ≤ (0 : Int) + d2817 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2064, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17227 p hg
    simpa only [d2064, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2064, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17518 p hg
    simpa only [d2064, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17520 (p : Pattern) (guard : d5537 p = 1) : d2065 p ≤ (0 : Int) + d2818 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2065, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17519 p hg
    simpa only [d2065, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2065, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2065, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17521 (p : Pattern) (guard : d5537 p = 1) : d2066 p ≤ (0 : Int) + d2819 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2066, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17520 p hg
    simpa only [d2066, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2066, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2066, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17522 (p : Pattern) (guard : d5537 p = 1) : d2067 p ≤ (0 : Int) + d2820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2067, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17509 p hg
    simpa only [d2067, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2067, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17521 p hg
    simpa only [d2067, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17523 (p : Pattern) (guard : d0 p = 1) : d2069 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17524 (p : Pattern) (guard : d5502 p = 1) : d2070 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2070, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d5502, d2070, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2070, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17523 p hg
    simpa only [d5502, d2070, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17525 (p : Pattern) (guard : d5502 p = 1) : d2071 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2071, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17124 p hg
    simpa only [d2071, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2071, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17524 p hg
    simpa only [d2071, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17526 (p : Pattern) (guard : d5537 p = 1) : d2072 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2072, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17525 p hg
    simpa only [d5537, d2072, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2072, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2072, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17527 (p : Pattern) (guard : d5537 p = 1) : d2073 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2073, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d2073, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2073, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17526 p hg
    simpa only [d2073, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17528 (p : Pattern) (guard : d5537 p = 1) : d2074 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17527 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17240 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17529 (p : Pattern) (guard : d5537 p = 1) : d2075 p ≤ (0 : Int) + d2821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2075, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17227 p hg
    simpa only [d2075, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2075, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17184 p hg
    simpa only [d2075, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17530 (p : Pattern) (guard : d5537 p = 1) : d2076 p ≤ (0 : Int) + d2822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2076, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17528 p hg
    simpa only [d2076, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2076, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17529 p hg
    simpa only [d2076, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17531 (p : Pattern) (guard : d5537 p = 1) : d2077 p ≤ (0 : Int) + d2823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2077, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17530 p hg
    simpa only [d2077, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2077, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17255 p hg
    simpa only [d2077, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17532 (p : Pattern) (guard : d5537 p = 1) : d2078 p ≤ (0 : Int) + d2824 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2078, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17518 p hg
    simpa only [d2078, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2078, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2078, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17533 (p : Pattern) (guard : d5537 p = 1) : d2079 p ≤ (0 : Int) + d2825 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2079, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17532 p hg
    simpa only [d2079, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2079, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2079, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17534 (p : Pattern) (guard : d5537 p = 1) : d2080 p ≤ (0 : Int) + d2826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2080, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17533 p hg
    simpa only [d2080, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2080, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2080, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17535 (p : Pattern) (guard : d5537 p = 1) : d2081 p ≤ (0 : Int) + d2827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2081, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17531 p hg
    simpa only [d2081, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2081, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17534 p hg
    simpa only [d2081, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17536 (p : Pattern) (guard : d5537 p = 1) : d2082 p ≤ (0 : Int) + d2828 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2082, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17522 p hg
    simpa only [d2082, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2082, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17535 p hg
    simpa only [d2082, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17537 (p : Pattern) (guard : d5537 p = 1) : d2083 p ≤ (0 : Int) + d2829 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2083, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17497 p hg
    simpa only [d2083, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2083, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17536 p hg
    simpa only [d2083, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17538 (p : Pattern) (guard : d5537 p = 1) : d2084 p ≤ (0 : Int) + d2830 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2084, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17536 p hg
    simpa only [d2084, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2084, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2084, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17539 (p : Pattern) (guard : d5537 p = 1) : d2085 p ≤ (0 : Int) + d2831 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2085, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17537 p hg
    simpa only [d2085, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2085, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17538 p hg
    simpa only [d2085, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17540 (p : Pattern) (guard : d5537 p = 1) : d2086 p ≤ (0 : Int) + d2832 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2086, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17297 p hg
    simpa only [d2086, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2086, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17539 p hg
    simpa only [d2086, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17541 (p : Pattern) (guard : d5537 p = 1) : d2087 p ≤ (0 : Int) + d2833 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2087, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17282 p hg
    simpa only [d2087, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2087, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17540 p hg
    simpa only [d2087, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17542 (p : Pattern) (guard : d5537 p = 1) : d2088 p ≤ (0 : Int) + d2834 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2088, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17328 p hg
    simpa only [d2088, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2088, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2088, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17543 (p : Pattern) (guard : d5537 p = 1) : d2089 p ≤ (0 : Int) + d2835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2089, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17371 p hg
    simpa only [d2089, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2089, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17542 p hg
    simpa only [d2089, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17544 (p : Pattern) (guard : d5537 p = 1) : d2090 p ≤ (0 : Int) + d2836 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2090, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17542 p hg
    simpa only [d2090, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2090, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2090, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17545 (p : Pattern) (guard : d5537 p = 1) : d2091 p ≤ (0 : Int) + d2837 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2091, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17543 p hg
    simpa only [d2091, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2091, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17544 p hg
    simpa only [d2091, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17546 (p : Pattern) (guard : d5537 p = 1) : d2092 p ≤ (0 : Int) + d2838 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2092, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17351 p hg
    simpa only [d2092, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2092, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2092, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17547 (p : Pattern) (guard : d5537 p = 1) : d2093 p ≤ (0 : Int) + d2839 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2093, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17378 p hg
    simpa only [d2093, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2093, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17546 p hg
    simpa only [d2093, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17548 (p : Pattern) (guard : d5537 p = 1) : d2094 p ≤ (0 : Int) + d2840 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2094, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17546 p hg
    simpa only [d2094, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2094, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2094, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17549 (p : Pattern) (guard : d5537 p = 1) : d2095 p ≤ (0 : Int) + d2841 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2095, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17547 p hg
    simpa only [d2095, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2095, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17548 p hg
    simpa only [d2095, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17550 (p : Pattern) (guard : d5537 p = 1) : d2096 p ≤ (0 : Int) + d2842 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2096, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17545 p hg
    simpa only [d2096, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2096, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17549 p hg
    simpa only [d2096, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17551 (p : Pattern) (guard : d5537 p = 1) : d2097 p ≤ (0 : Int) + d2843 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2097, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17357 p hg
    simpa only [d2097, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2097, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17550 p hg
    simpa only [d2097, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17552 (p : Pattern) (guard : d5537 p = 1) : d2098 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2098, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17413 p hg
    simpa only [d2098, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2098, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2098, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17553 (p : Pattern) (guard : d5537 p = 1) : d2099 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2099, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17426 p hg
    simpa only [d2099, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2099, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17552 p hg
    simpa only [d2099, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17554 (p : Pattern) (guard : d5537 p = 1) : d2100 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2100, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17552 p hg
    simpa only [d2100, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2100, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2100, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17555 (p : Pattern) (guard : d5537 p = 1) : d2101 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2101, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17553 p hg
    simpa only [d2101, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2101, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17554 p hg
    simpa only [d2101, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17556 (p : Pattern) (guard : d5537 p = 1) : d2102 p ≤ (0 : Int) + d2848 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2102, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17555 p hg
    simpa only [d2102, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2102, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17434 p hg
    simpa only [d2102, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17557 (p : Pattern) (guard : d5537 p = 1) : d2103 p ≤ (0 : Int) + d2849 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2103, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17425 p hg
    simpa only [d2103, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2103, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17556 p hg
    simpa only [d2103, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17558 (p : Pattern) (guard : d5537 p = 1) : d2104 p ≤ (0 : Int) + d2850 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2104, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17551 p hg
    simpa only [d2104, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2104, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17557 p hg
    simpa only [d2104, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17559 (p : Pattern) (guard : d5537 p = 1) : d2105 p ≤ (0 : Int) + d2851 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2105, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17557 p hg
    simpa only [d2105, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2105, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17441 p hg
    simpa only [d2105, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17560 (p : Pattern) (guard : d5537 p = 1) : d2106 p ≤ (0 : Int) + d2852 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2106, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17558 p hg
    simpa only [d2106, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2106, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17559 p hg
    simpa only [d2106, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17561 (p : Pattern) (guard : d5502 p = 1) : d2107 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2107, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d2107, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2107, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17393 p hg
    simpa only [d5502, d2107, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17562 (p : Pattern) (guard : d5502 p = 1) : d2108 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2108, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17394 p hg
    simpa only [d2108, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2108, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17561 p hg
    simpa only [d2108, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17563 (p : Pattern) (guard : d5537 p = 1) : d2109 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2109, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17562 p hg
    simpa only [d5537, d2109, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2109, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2109, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17564 (p : Pattern) (guard : d5537 p = 1) : d2110 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2110, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d2110, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2110, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17563 p hg
    simpa only [d2110, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17565 (p : Pattern) (guard : d5537 p = 1) : d2111 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2111, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17564 p hg
    simpa only [d2111, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2111, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17413 p hg
    simpa only [d2111, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17566 (p : Pattern) (guard : d5537 p = 1) : d2112 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2112, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17392 p hg
    simpa only [d2112, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2112, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17565 p hg
    simpa only [d2112, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17567 (p : Pattern) (guard : d5537 p = 1) : d2113 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2113, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17399 p hg
    simpa only [d2113, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2113, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17413 p hg
    simpa only [d2113, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17568 (p : Pattern) (guard : d5537 p = 1) : d2114 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2114, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17567 p hg
    simpa only [d2114, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2114, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17331 p hg
    simpa only [d2114, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17569 (p : Pattern) (guard : d5537 p = 1) : d2115 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2115, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17566 p hg
    simpa only [d2115, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2115, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17568 p hg
    simpa only [d2115, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17570 (p : Pattern) (guard : d5537 p = 1) : d2116 p ≤ (0 : Int) + d2853 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2116, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17363 p hg
    simpa only [d2116, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2116, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17347 p hg
    simpa only [d2116, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17571 (p : Pattern) (guard : d5537 p = 1) : d2117 p ≤ (0 : Int) + d2854 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2117, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17418 p hg
    simpa only [d2117, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2117, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17570 p hg
    simpa only [d2117, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17572 (p : Pattern) (guard : d5537 p = 1) : d2118 p ≤ (0 : Int) + d2855 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2118, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17571 p hg
    simpa only [d2118, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2118, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17546 p hg
    simpa only [d2118, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17573 (p : Pattern) (guard : d5537 p = 1) : d2119 p ≤ (0 : Int) + d2856 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2119, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17420 p hg
    simpa only [d2119, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2119, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2119, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17574 (p : Pattern) (guard : d5537 p = 1) : d2120 p ≤ (0 : Int) + d2857 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2120, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17573 p hg
    simpa only [d2120, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2120, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2120, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17575 (p : Pattern) (guard : d5537 p = 1) : d2121 p ≤ (0 : Int) + d2858 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2121, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17574 p hg
    simpa only [d2121, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2121, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2121, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17576 (p : Pattern) (guard : d5537 p = 1) : d2122 p ≤ (0 : Int) + d2859 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2122, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17572 p hg
    simpa only [d2122, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2122, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17575 p hg
    simpa only [d2122, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17577 (p : Pattern) (guard : d5537 p = 1) : d2123 p ≤ (0 : Int) + d2860 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2123, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17569 p hg
    simpa only [d2123, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2123, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17576 p hg
    simpa only [d2123, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17578 (p : Pattern) (guard : d0 p = 1) : d1895 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17579 (p : Pattern) (guard : d5502 p = 1) : d2124 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2124, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d5502, d2124, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2124, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17578 p hg
    simpa only [d5502, d2124, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17580 (p : Pattern) (guard : d5502 p = 1) : d1895 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17578 p hg
    simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17581 (p : Pattern) (guard : d5502 p = 1) : d2125 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2125, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17579 p hg
    simpa only [d2125, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2125, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17580 p hg
    simpa only [d2125, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17582 (p : Pattern) (guard : d5537 p = 1) : d2126 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2126, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17581 p hg
    simpa only [d5537, d2126, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2126, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2126, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17583 (p : Pattern) (guard : d5537 p = 1) : d2127 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2127, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17363 p hg
    simpa only [d2127, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2127, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17582 p hg
    simpa only [d2127, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17584 (p : Pattern) (guard : d5537 p = 1) : d2128 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2128, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17564 p hg
    simpa only [d2128, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2128, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17583 p hg
    simpa only [d2128, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17585 (p : Pattern) (guard : d0 p = 1) : d1964 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17586 (p : Pattern) (guard : d5502 p = 1) : d2129 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2129, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d5502, d2129, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2129, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17585 p hg
    simpa only [d5502, d2129, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17587 (p : Pattern) (guard : d5502 p = 1) : d1964 p ≤ (0 : Int) + d2690 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17408 p hg
    simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17585 p hg
    simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17588 (p : Pattern) (guard : d5502 p = 1) : d2130 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2130, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17586 p hg
    simpa only [d2130, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2130, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17587 p hg
    simpa only [d2130, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17589 (p : Pattern) (guard : d5537 p = 1) : d2131 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2131, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17588 p hg
    simpa only [d5537, d2131, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2131, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2131, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17590 (p : Pattern) (guard : d5537 p = 1) : d2132 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2132, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17321 p hg
    simpa only [d2132, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2132, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17589 p hg
    simpa only [d2132, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17591 (p : Pattern) (guard : d5537 p = 1) : d2133 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2133, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17590 p hg
    simpa only [d2133, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2133, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2133, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17592 (p : Pattern) (guard : d5537 p = 1) : d2134 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2134, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17584 p hg
    simpa only [d2134, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2134, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17591 p hg
    simpa only [d2134, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17593 (p : Pattern) (guard : d5502 p = 1) : d2135 p ≤ (0 : Int) + d2690 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2135, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17408 p hg
    simpa only [d5502, d2135, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2135, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17406 p hg
    simpa only [d5502, d2135, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17594 (p : Pattern) (guard : d5502 p = 1) : d2136 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2136, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17407 p hg
    simpa only [d2136, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2136, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17593 p hg
    simpa only [d2136, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17595 (p : Pattern) (guard : d5537 p = 1) : d2137 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2137, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17594 p hg
    simpa only [d5537, d2137, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2137, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2137, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17596 (p : Pattern) (guard : d5537 p = 1) : d2138 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2138, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17321 p hg
    simpa only [d2138, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2138, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17595 p hg
    simpa only [d2138, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17597 (p : Pattern) (guard : d5537 p = 1) : d2139 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2139, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17596 p hg
    simpa only [d2139, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2139, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2139, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17598 (p : Pattern) (guard : d5537 p = 1) : d2140 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2140, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17597 p hg
    simpa only [d2140, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2140, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2140, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17599 (p : Pattern) (guard : d5537 p = 1) : d2141 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2141, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17592 p hg
    simpa only [d2141, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2141, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17598 p hg
    simpa only [d2141, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17600 (p : Pattern) (guard : d5537 p = 1) : d2142 p ≤ (0 : Int) + d2861 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2142, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17321 p hg
    simpa only [d2142, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2142, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17347 p hg
    simpa only [d2142, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17601 (p : Pattern) (guard : d5537 p = 1) : d2143 p ≤ (0 : Int) + d2862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2143, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17600 p hg
    simpa only [d2143, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2143, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17351 p hg
    simpa only [d2143, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17602 (p : Pattern) (guard : d5537 p = 1) : d2144 p ≤ (0 : Int) + d2863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2144, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17601 p hg
    simpa only [d2144, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2144, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17574 p hg
    simpa only [d2144, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17603 (p : Pattern) (guard : d5537 p = 1) : d2145 p ≤ (0 : Int) + d2864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2145, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17152 p hg
    simpa only [d2145, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2145, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2145, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17604 (p : Pattern) (guard : d5537 p = 1) : d2146 p ≤ (0 : Int) + d2865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2146, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17602 p hg
    simpa only [d2146, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2146, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17603 p hg
    simpa only [d2146, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17605 (p : Pattern) (guard : d5537 p = 1) : d2147 p ≤ (0 : Int) + d2866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2147, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17599 p hg
    simpa only [d2147, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2147, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17604 p hg
    simpa only [d2147, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17606 (p : Pattern) (guard : d5537 p = 1) : d2148 p ≤ (0 : Int) + d2867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2148, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17577 p hg
    simpa only [d2148, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2148, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17605 p hg
    simpa only [d2148, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17607 (p : Pattern) (guard : d5537 p = 1) : d2149 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17399 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17405 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17608 (p : Pattern) (guard : d5537 p = 1) : d2150 p ≤ (0 : Int) + d2868 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2150, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17418 p hg
    simpa only [d2150, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2150, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17184 p hg
    simpa only [d2150, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17609 (p : Pattern) (guard : d5537 p = 1) : d2151 p ≤ (0 : Int) + d2869 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2151, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17607 p hg
    simpa only [d2151, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2151, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17608 p hg
    simpa only [d2151, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17610 (p : Pattern) (guard : d5537 p = 1) : d2152 p ≤ (0 : Int) + d2870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2152, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17609 p hg
    simpa only [d2152, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2152, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17430 p hg
    simpa only [d2152, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17611 (p : Pattern) (guard : d5537 p = 1) : d2153 p ≤ (0 : Int) + d2871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2153, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17610 p hg
    simpa only [d2153, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2153, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17434 p hg
    simpa only [d2153, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17612 (p : Pattern) (guard : d0 p = 1) : d2155 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17613 (p : Pattern) (guard : d5502 p = 1) : d2156 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2156, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d5502, d2156, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2156, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17612 p hg
    simpa only [d5502, d2156, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17614 (p : Pattern) (guard : d5502 p = 1) : d2157 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2157, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17335 p hg
    simpa only [d2157, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2157, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17613 p hg
    simpa only [d2157, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17615 (p : Pattern) (guard : d5537 p = 1) : d2158 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2158, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17614 p hg
    simpa only [d5537, d2158, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2158, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2158, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17616 (p : Pattern) (guard : d5537 p = 1) : d2159 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2159, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17363 p hg
    simpa only [d2159, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2159, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17615 p hg
    simpa only [d2159, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17617 (p : Pattern) (guard : d5537 p = 1) : d2160 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17616 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17418 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17618 (p : Pattern) (guard : d5537 p = 1) : d2161 p ≤ (0 : Int) + d2872 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2161, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17617 p hg
    simpa only [d2161, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2161, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17552 p hg
    simpa only [d2161, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17619 (p : Pattern) (guard : d5537 p = 1) : d2162 p ≤ (0 : Int) + d2873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2162, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17618 p hg
    simpa only [d2162, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2162, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17433 p hg
    simpa only [d2162, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17620 (p : Pattern) (guard : d5537 p = 1) : d2163 p ≤ (0 : Int) + d2874 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2163, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17237 p hg
    simpa only [d2163, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2163, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2163, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17621 (p : Pattern) (guard : d5537 p = 1) : d2164 p ≤ (0 : Int) + d2875 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2164, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17620 p hg
    simpa only [d2164, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2164, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2164, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17622 (p : Pattern) (guard : d5537 p = 1) : d2165 p ≤ (0 : Int) + d2876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2165, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17619 p hg
    simpa only [d2165, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2165, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17621 p hg
    simpa only [d2165, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17623 (p : Pattern) (guard : d5537 p = 1) : d2166 p ≤ (0 : Int) + d2877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2166, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17611 p hg
    simpa only [d2166, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2166, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17622 p hg
    simpa only [d2166, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17624 (p : Pattern) (guard : d5537 p = 1) : d2167 p ≤ (0 : Int) + d2878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2167, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17606 p hg
    simpa only [d2167, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2167, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17623 p hg
    simpa only [d2167, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17625 (p : Pattern) (guard : d5537 p = 1) : d2168 p ≤ (0 : Int) + d2879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2168, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17418 p hg
    simpa only [d2168, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2168, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17236 p hg
    simpa only [d2168, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17626 (p : Pattern) (guard : d5537 p = 1) : d2169 p ≤ (0 : Int) + d2880 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2169, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17607 p hg
    simpa only [d2169, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2169, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17625 p hg
    simpa only [d2169, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17627 (p : Pattern) (guard : d5537 p = 1) : d2170 p ≤ (0 : Int) + d2881 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2170, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17413 p hg
    simpa only [d2170, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2170, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17236 p hg
    simpa only [d2170, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17628 (p : Pattern) (guard : d5537 p = 1) : d2171 p ≤ (0 : Int) + d2882 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2171, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17627 p hg
    simpa only [d2171, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2171, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2171, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17629 (p : Pattern) (guard : d5537 p = 1) : d2172 p ≤ (0 : Int) + d2883 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2172, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17626 p hg
    simpa only [d2172, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2172, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17628 p hg
    simpa only [d2172, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17630 (p : Pattern) (guard : d5537 p = 1) : d2173 p ≤ (0 : Int) + d2884 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2173, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17421 p hg
    simpa only [d2173, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2173, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17184 p hg
    simpa only [d2173, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17631 (p : Pattern) (guard : d5537 p = 1) : d2174 p ≤ (0 : Int) + d2885 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2174, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17630 p hg
    simpa only [d2174, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2174, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2174, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17632 (p : Pattern) (guard : d5537 p = 1) : d2175 p ≤ (0 : Int) + d2886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2175, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17631 p hg
    simpa only [d2175, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2175, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2175, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17633 (p : Pattern) (guard : d5537 p = 1) : d2176 p ≤ (0 : Int) + d2887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2176, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17629 p hg
    simpa only [d2176, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2176, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17632 p hg
    simpa only [d2176, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17634 (p : Pattern) (guard : d5537 p = 1) : d2177 p ≤ (0 : Int) + d2888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2177, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17633 p hg
    simpa only [d2177, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2177, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17622 p hg
    simpa only [d2177, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17635 (p : Pattern) (guard : d5537 p = 1) : d2178 p ≤ (0 : Int) + d2889 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2178, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17634 p hg
    simpa only [d2178, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2178, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2178, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17636 (p : Pattern) (guard : d5537 p = 1) : d2179 p ≤ (0 : Int) + d2890 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2179, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17624 p hg
    simpa only [d2179, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2179, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17635 p hg
    simpa only [d2179, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17637 (p : Pattern) (guard : d5537 p = 1) : d2180 p ≤ (0 : Int) + d2891 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2180, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17560 p hg
    simpa only [d2180, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2180, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17636 p hg
    simpa only [d2180, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17638 (p : Pattern) (guard : d5537 p = 1) : d2181 p ≤ (0 : Int) + d2892 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2181, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17282 p hg
    simpa only [d2181, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2181, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17637 p hg
    simpa only [d2181, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17639 (p : Pattern) (guard : d5537 p = 1) : d2182 p ≤ (0 : Int) + d2893 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2182, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17541 p hg
    simpa only [d2182, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2182, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17638 p hg
    simpa only [d2182, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
