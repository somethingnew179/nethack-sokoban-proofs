/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2520 (p : Pattern) (guard : d841 p = 1) : d265 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d265, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2516 p hg
    simpa only [d265, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d265, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2519 p hg
    simpa only [d265, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2521 (p : Pattern) (guard : d0 p = 1) : d285 p ≤ (0 : Int) + d165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2522 (p : Pattern) (guard : d870 p = 1) : d286 p ≤ (0 : Int) + d180 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d870, d286, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2520 p hg
    simpa only [d870, d286, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d870, d286, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2521 p hg
    simpa only [d870, d286, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2523 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2524 (p : Pattern) (guard : d841 p = 1) : d273 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d273, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare559 p hg
    simpa only [d841, d273, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d273, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2523 p hg
    simpa only [d841, d273, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2525 (p : Pattern) (guard : d841 p = 1) : d274 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d274, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2515 p hg
    simpa only [d274, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d274, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2524 p hg
    simpa only [d274, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2526 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2527 (p : Pattern) (guard : d841 p = 1) : d275 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d841, d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2526 p hg
    simpa only [d841, d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2528 (p : Pattern) (guard : d841 p = 1) : d276 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2508 p hg
    simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2529 (p : Pattern) (guard : d841 p = 1) : d277 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d277, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2525 p hg
    simpa only [d277, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d277, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d277, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2530 (p : Pattern) (guard : d0 p = 1) : d289 p ≤ (0 : Int) + d170 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2531 (p : Pattern) (guard : d870 p = 1) : d290 p ≤ (0 : Int) + d181 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d870, d290, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d870, d290, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d870, d290, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d870, d290, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2532 (p : Pattern) (guard : d870 p = 1) : d291 p ≤ (0 : Int) + d182 p := by
  cases selected : p 86 with
  | false =>
    have hg : d870 p = 1 := by simpa only [d291, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2522 p hg
    simpa only [d291, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d870 p = 1 := by simpa only [d291, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2531 p hg
    simpa only [d291, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2533 (p : Pattern) (guard : d870 p = 1) : d292 p ≤ (0 : Int) + d183 p := by
  cases selected : p 80 with
  | false =>
    have hg : d870 p = 1 := by simpa only [d292, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d292, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d870 p = 1 := by simpa only [d292, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2532 p hg
    simpa only [d292, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2534 (p : Pattern) (guard : d0 p = 1) : d260 p ≤ (1 : Int) + d67 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2535 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (1 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2536 (p : Pattern) (guard : d841 p = 1) : d256 p ≤ (1 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d256, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2 p hg
    simpa only [d841, d256, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d256, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d841, d256, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2537 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (1 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2538 (p : Pattern) (guard : d841 p = 1) : d261 p ≤ (1 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d261, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2 p hg
    simpa only [d841, d261, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d261, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2537 p hg
    simpa only [d841, d261, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2539 (p : Pattern) (guard : d841 p = 1) : d262 p ≤ (1 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2536 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2538 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2540 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (1 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2541 (p : Pattern) (guard : d841 p = 1) : d257 p ≤ (1 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d257, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare141 p hg
    simpa only [d841, d257, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d257, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2540 p hg
    simpa only [d841, d257, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2542 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (1 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2543 (p : Pattern) (guard : d841 p = 1) : d263 p ≤ (1 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d263, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare147 p hg
    simpa only [d841, d263, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d263, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2542 p hg
    simpa only [d841, d263, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2544 (p : Pattern) (guard : d841 p = 1) : d264 p ≤ (1 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d264, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2541 p hg
    simpa only [d264, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d264, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d264, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2545 (p : Pattern) (guard : d841 p = 1) : d265 p ≤ (1 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d265, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2539 p hg
    simpa only [d265, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d265, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2544 p hg
    simpa only [d265, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2546 (p : Pattern) (guard : d842 p = 1) : d266 p ≤ (1 : Int) + d67 p := by
  cases selected : p 106 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d842, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2534 p hg
    simpa only [d842, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d842, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2545 p hg
    simpa only [d842, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2547 (p : Pattern) (guard : d0 p = 1) : d272 p ≤ (1 : Int) + d128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2548 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (1 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2549 (p : Pattern) (guard : d841 p = 1) : d273 p ≤ (1 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d273, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33 p hg
    simpa only [d841, d273, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d273, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2548 p hg
    simpa only [d841, d273, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2550 (p : Pattern) (guard : d841 p = 1) : d274 p ≤ (1 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d274, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2538 p hg
    simpa only [d274, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d274, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2549 p hg
    simpa only [d274, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2551 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2552 (p : Pattern) (guard : d841 p = 1) : d270 p ≤ (1 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d270, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare172 p hg
    simpa only [d841, d270, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d270, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2551 p hg
    simpa only [d841, d270, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2553 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2554 (p : Pattern) (guard : d841 p = 1) : d275 p ≤ (1 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare180 p hg
    simpa only [d841, d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2553 p hg
    simpa only [d841, d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2555 (p : Pattern) (guard : d841 p = 1) : d276 p ≤ (1 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2552 p hg
    simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2554 p hg
    simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2556 (p : Pattern) (guard : d841 p = 1) : d277 p ≤ (1 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d277, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d277, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d277, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2555 p hg
    simpa only [d277, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2557 (p : Pattern) (guard : d842 p = 1) : d278 p ≤ (1 : Int) + d128 p := by
  cases selected : p 106 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d842, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2547 p hg
    simpa only [d842, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d842, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2556 p hg
    simpa only [d842, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2558 (p : Pattern) (guard : d842 p = 1) : d279 p ≤ (1 : Int) + d1147 p := by
  cases selected : p 86 with
  | false =>
    have hg : d842 p = 1 := by simpa only [d279, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2546 p hg
    simpa only [d279, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d842 p = 1 := by simpa only [d279, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2557 p hg
    simpa only [d279, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2559 (p : Pattern) (guard : d0 p = 1) : d291 p ≤ (1 : Int) + d1147 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2560 (p : Pattern) (guard : d843 p = 1) : d292 p ≤ (1 : Int) + d1147 p := by
  cases selected : p 80 with
  | false =>
    have hg : d842 p = 1 := by simpa only [d843, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2558 p hg
    simpa only [d843, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d843, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2559 p hg
    simpa only [d843, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2561 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d555 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2562 (p : Pattern) (guard : d1148 p = 1) : d256 p ≤ (0 : Int) + d556 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d256, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d1148, d256, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d256, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2561 p hg
    simpa only [d1148, d256, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2563 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d560 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2564 (p : Pattern) (guard : d1148 p = 1) : d257 p ≤ (0 : Int) + d561 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d257, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2385 p hg
    simpa only [d1148, d257, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d257, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2563 p hg
    simpa only [d1148, d257, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2565 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d571 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2566 (p : Pattern) (guard : d1148 p = 1) : d258 p ≤ (0 : Int) + d572 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d258, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d1148, d258, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d258, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2565 p hg
    simpa only [d1148, d258, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2567 (p : Pattern) (guard : d1148 p = 1) : d259 p ≤ (0 : Int) + d573 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d259, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2564 p hg
    simpa only [d259, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d259, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2566 p hg
    simpa only [d259, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2568 (p : Pattern) (guard : d1148 p = 1) : d260 p ≤ (0 : Int) + d574 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d260, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2562 p hg
    simpa only [d260, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d260, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2567 p hg
    simpa only [d260, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2569 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d581 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2570 (p : Pattern) (guard : d1148 p = 1) : d256 p ≤ (0 : Int) + d582 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d256, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d1148, d256, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d256, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2569 p hg
    simpa only [d1148, d256, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2571 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d587 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2572 (p : Pattern) (guard : d1148 p = 1) : d261 p ≤ (0 : Int) + d588 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d261, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d1148, d261, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d261, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2571 p hg
    simpa only [d1148, d261, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2573 (p : Pattern) (guard : d1148 p = 1) : d262 p ≤ (0 : Int) + d589 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d262, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2570 p hg
    simpa only [d262, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d262, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d262, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2574 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d590 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2575 (p : Pattern) (guard : d1148 p = 1) : d257 p ≤ (0 : Int) + d591 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d257, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2385 p hg
    simpa only [d1148, d257, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d257, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d1148, d257, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2576 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d592 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2577 (p : Pattern) (guard : d1148 p = 1) : d263 p ≤ (0 : Int) + d593 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d263, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d1148, d263, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d263, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2576 p hg
    simpa only [d1148, d263, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2578 (p : Pattern) (guard : d1148 p = 1) : d264 p ≤ (0 : Int) + d594 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d264, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2575 p hg
    simpa only [d264, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d264, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2577 p hg
    simpa only [d264, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2579 (p : Pattern) (guard : d1148 p = 1) : d265 p ≤ (0 : Int) + d595 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d265, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2573 p hg
    simpa only [d265, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d265, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d265, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2580 (p : Pattern) (guard : d1148 p = 1) : d266 p ≤ (0 : Int) + d596 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d266, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2568 p hg
    simpa only [d266, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d266, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2579 p hg
    simpa only [d266, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2581 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d606 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2582 (p : Pattern) (guard : d1148 p = 1) : d267 p ≤ (0 : Int) + d607 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d267, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2433 p hg
    simpa only [d1148, d267, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d267, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2581 p hg
    simpa only [d1148, d267, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2583 (p : Pattern) (guard : d1148 p = 1) : d268 p ≤ (0 : Int) + d608 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d268, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2562 p hg
    simpa only [d268, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d268, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2582 p hg
    simpa only [d268, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2584 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d580 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2585 (p : Pattern) (guard : d1148 p = 1) : d269 p ≤ (0 : Int) + d610 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d269, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d1148, d269, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d269, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2584 p hg
    simpa only [d1148, d269, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2586 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d580 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2587 (p : Pattern) (guard : d1148 p = 1) : d270 p ≤ (0 : Int) + d610 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d270, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d1148, d270, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d270, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2586 p hg
    simpa only [d1148, d270, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2588 (p : Pattern) (guard : d1148 p = 1) : d271 p ≤ (0 : Int) + d610 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2585 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2587 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2589 (p : Pattern) (guard : d1148 p = 1) : d272 p ≤ (0 : Int) + d611 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d272, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2583 p hg
    simpa only [d272, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d272, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2588 p hg
    simpa only [d272, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2590 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d614 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2591 (p : Pattern) (guard : d1148 p = 1) : d273 p ≤ (0 : Int) + d615 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d273, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2450 p hg
    simpa only [d1148, d273, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d273, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2590 p hg
    simpa only [d1148, d273, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2592 (p : Pattern) (guard : d1148 p = 1) : d274 p ≤ (0 : Int) + d616 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d274, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d274, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d274, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2591 p hg
    simpa only [d274, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2593 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2594 (p : Pattern) (guard : d1148 p = 1) : d270 p ≤ (0 : Int) + d618 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d270, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d1148, d270, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d270, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2593 p hg
    simpa only [d1148, d270, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2595 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d620 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2596 (p : Pattern) (guard : d1148 p = 1) : d275 p ≤ (0 : Int) + d621 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d275, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2457 p hg
    simpa only [d1148, d275, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d275, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2595 p hg
    simpa only [d1148, d275, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2597 (p : Pattern) (guard : d1148 p = 1) : d276 p ≤ (0 : Int) + d622 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d276, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2594 p hg
    simpa only [d276, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d276, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d276, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2598 (p : Pattern) (guard : d1148 p = 1) : d277 p ≤ (0 : Int) + d623 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d277, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d277, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d277, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d277, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2599 (p : Pattern) (guard : d1148 p = 1) : d278 p ≤ (0 : Int) + d624 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d278, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d278, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d278, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2598 p hg
    simpa only [d278, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2600 (p : Pattern) (guard : d1148 p = 1) : d279 p ≤ (0 : Int) + d625 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d279, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2580 p hg
    simpa only [d279, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d279, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2599 p hg
    simpa only [d279, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2601 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d627 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2602 (p : Pattern) (guard : d1148 p = 1) : d261 p ≤ (0 : Int) + d628 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d261, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d1148, d261, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d261, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2601 p hg
    simpa only [d1148, d261, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2603 (p : Pattern) (guard : d1148 p = 1) : d262 p ≤ (0 : Int) + d629 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d262, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2562 p hg
    simpa only [d262, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d262, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2602 p hg
    simpa only [d262, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2604 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d571 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2605 (p : Pattern) (guard : d1148 p = 1) : d263 p ≤ (0 : Int) + d572 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d263, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d1148, d263, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d263, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2604 p hg
    simpa only [d1148, d263, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2606 (p : Pattern) (guard : d1148 p = 1) : d264 p ≤ (0 : Int) + d573 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d264, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2564 p hg
    simpa only [d264, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d264, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2605 p hg
    simpa only [d264, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2607 (p : Pattern) (guard : d1148 p = 1) : d265 p ≤ (0 : Int) + d630 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d265, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2603 p hg
    simpa only [d265, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d265, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2606 p hg
    simpa only [d265, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2608 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2609 (p : Pattern) (guard : d1148 p = 1) : d280 p ≤ (0 : Int) + d634 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d280, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2470 p hg
    simpa only [d1148, d280, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d280, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2608 p hg
    simpa only [d1148, d280, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2610 (p : Pattern) (guard : d1148 p = 1) : d281 p ≤ (0 : Int) + d635 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d281, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d281, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d281, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d281, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2611 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d590 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2612 (p : Pattern) (guard : d1148 p = 1) : d282 p ≤ (0 : Int) + d591 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d282, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2385 p hg
    simpa only [d1148, d282, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d282, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2611 p hg
    simpa only [d1148, d282, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2613 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d592 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2614 (p : Pattern) (guard : d1148 p = 1) : d283 p ≤ (0 : Int) + d593 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d283, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d1148, d283, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d283, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2613 p hg
    simpa only [d1148, d283, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2615 (p : Pattern) (guard : d1148 p = 1) : d284 p ≤ (0 : Int) + d594 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d284, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2612 p hg
    simpa only [d284, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d284, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2614 p hg
    simpa only [d284, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2616 (p : Pattern) (guard : d1148 p = 1) : d285 p ≤ (0 : Int) + d636 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d285, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2610 p hg
    simpa only [d285, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d285, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2615 p hg
    simpa only [d285, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2617 (p : Pattern) (guard : d1148 p = 1) : d286 p ≤ (0 : Int) + d637 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d286, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2607 p hg
    simpa only [d286, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d286, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2616 p hg
    simpa only [d286, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2618 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d641 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2619 (p : Pattern) (guard : d1148 p = 1) : d273 p ≤ (0 : Int) + d642 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d273, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2450 p hg
    simpa only [d1148, d273, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d273, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2618 p hg
    simpa only [d1148, d273, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2620 (p : Pattern) (guard : d1148 p = 1) : d274 p ≤ (0 : Int) + d643 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d274, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2602 p hg
    simpa only [d274, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d274, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d274, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2621 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d586 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2622 (p : Pattern) (guard : d1148 p = 1) : d275 p ≤ (0 : Int) + d644 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d275, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2457 p hg
    simpa only [d1148, d275, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d275, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d1148, d275, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2623 (p : Pattern) (guard : d1148 p = 1) : d276 p ≤ (0 : Int) + d645 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d276, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2587 p hg
    simpa only [d276, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d276, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2622 p hg
    simpa only [d276, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2624 (p : Pattern) (guard : d1148 p = 1) : d277 p ≤ (0 : Int) + d646 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d277, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2620 p hg
    simpa only [d277, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d277, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2623 p hg
    simpa only [d277, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2625 (p : Pattern) (guard : d1148 p = 1) : d287 p ≤ (0 : Int) + d647 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d287, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d287, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d287, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2614 p hg
    simpa only [d287, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2626 (p : Pattern) (guard : d1148 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2627 (p : Pattern) (guard : d1148 p = 1) : d288 p ≤ (0 : Int) + d648 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d288, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d288, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d288, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2626 p hg
    simpa only [d288, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2628 (p : Pattern) (guard : d1148 p = 1) : d289 p ≤ (0 : Int) + d649 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d289, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2625 p hg
    simpa only [d289, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d289, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2627 p hg
    simpa only [d289, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2629 (p : Pattern) (guard : d1148 p = 1) : d290 p ≤ (0 : Int) + d650 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d290, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2624 p hg
    simpa only [d290, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d290, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2628 p hg
    simpa only [d290, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2630 (p : Pattern) (guard : d1148 p = 1) : d291 p ≤ (0 : Int) + d651 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d291, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2617 p hg
    simpa only [d291, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d291, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2629 p hg
    simpa only [d291, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2631 (p : Pattern) (guard : d1148 p = 1) : d292 p ≤ (0 : Int) + d652 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d292, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2600 p hg
    simpa only [d292, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d292, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2630 p hg
    simpa only [d292, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2632 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d293 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2633 (p : Pattern) (guard : d912 p = 1) : d256 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d912, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2632 p hg
    simpa only [d912, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2634 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d294 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2635 (p : Pattern) (guard : d912 p = 1) : d257 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare793 p hg
    simpa only [d912, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2634 p hg
    simpa only [d912, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2636 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2637 (p : Pattern) (guard : d912 p = 1) : d258 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare798 p hg
    simpa only [d912, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2636 p hg
    simpa only [d912, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2638 (p : Pattern) (guard : d912 p = 1) : d259 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d259, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2635 p hg
    simpa only [d259, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d259, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2637 p hg
    simpa only [d259, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2639 (p : Pattern) (guard : d912 p = 1) : d260 p ≤ (0 : Int) + d297 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d260, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2633 p hg
    simpa only [d260, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d260, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2638 p hg
    simpa only [d260, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2640 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2641 (p : Pattern) (guard : d912 p = 1) : d261 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d261, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d912, d261, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d261, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2640 p hg
    simpa only [d912, d261, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2642 (p : Pattern) (guard : d912 p = 1) : d262 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d262, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2633 p hg
    simpa only [d262, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d262, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d262, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2643 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2644 (p : Pattern) (guard : d912 p = 1) : d263 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare798 p hg
    simpa only [d912, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d912, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2645 (p : Pattern) (guard : d912 p = 1) : d264 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d264, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2635 p hg
    simpa only [d264, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d264, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2644 p hg
    simpa only [d264, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2646 (p : Pattern) (guard : d912 p = 1) : d265 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d265, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2642 p hg
    simpa only [d265, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d265, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d265, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2647 (p : Pattern) (guard : d912 p = 1) : d266 p ≤ (0 : Int) + d302 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d266, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2639 p hg
    simpa only [d266, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d266, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2646 p hg
    simpa only [d266, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2648 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2649 (p : Pattern) (guard : d912 p = 1) : d267 p ≤ (0 : Int) + d305 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d267, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare807 p hg
    simpa only [d912, d267, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d267, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2648 p hg
    simpa only [d912, d267, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2650 (p : Pattern) (guard : d912 p = 1) : d268 p ≤ (0 : Int) + d306 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d268, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2633 p hg
    simpa only [d268, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d268, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2649 p hg
    simpa only [d268, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2651 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d307 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2652 (p : Pattern) (guard : d912 p = 1) : d269 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d912, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d912, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2653 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d307 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2654 (p : Pattern) (guard : d912 p = 1) : d270 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d912, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d912, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2655 (p : Pattern) (guard : d912 p = 1) : d271 p ≤ (0 : Int) + d307 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2652 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2654 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2656 (p : Pattern) (guard : d912 p = 1) : d272 p ≤ (0 : Int) + d308 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d272, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2650 p hg
    simpa only [d272, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d272, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2655 p hg
    simpa only [d272, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2657 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (0 : Int) + d309 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2658 (p : Pattern) (guard : d912 p = 1) : d273 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d273, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare827 p hg
    simpa only [d912, d273, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d273, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2657 p hg
    simpa only [d912, d273, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2659 (p : Pattern) (guard : d912 p = 1) : d274 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d274, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d274, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d274, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2658 p hg
    simpa only [d274, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
