/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons160
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22540 (p : Pattern) (guard : d5538 p = 1) : d2882 p ≤ (4 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2882, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22539 p hg
    simpa only [d2882, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2882, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2882, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22541 (p : Pattern) (guard : d5538 p = 1) : d2883 p ≤ (4 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2883, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22538 p hg
    simpa only [d2883, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2883, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22540 p hg
    simpa only [d2883, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22542 (p : Pattern) (guard : d5538 p = 1) : d2884 p ≤ (4 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2884, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22403 p hg
    simpa only [d2884, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2884, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d2884, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22543 (p : Pattern) (guard : d5538 p = 1) : d2885 p ≤ (4 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2885, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22542 p hg
    simpa only [d2885, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2885, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2885, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22544 (p : Pattern) (guard : d5538 p = 1) : d2886 p ≤ (4 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2886, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22543 p hg
    simpa only [d2886, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2886, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2886, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22545 (p : Pattern) (guard : d5538 p = 1) : d2887 p ≤ (4 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2887, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22541 p hg
    simpa only [d2887, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2887, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22544 p hg
    simpa only [d2887, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22546 (p : Pattern) (guard : d5538 p = 1) : d2888 p ≤ (4 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2888, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22545 p hg
    simpa only [d2888, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2888, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22534 p hg
    simpa only [d2888, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22547 (p : Pattern) (guard : d5538 p = 1) : d2889 p ≤ (4 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2889, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22546 p hg
    simpa only [d2889, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2889, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2889, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22548 (p : Pattern) (guard : d5538 p = 1) : d2890 p ≤ (4 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2890, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22536 p hg
    simpa only [d2890, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2890, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22547 p hg
    simpa only [d2890, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22549 (p : Pattern) (guard : d5538 p = 1) : d2891 p ≤ (4 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2891, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22510 p hg
    simpa only [d2891, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2891, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22548 p hg
    simpa only [d2891, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22550 (p : Pattern) (guard : d5538 p = 1) : d2892 p ≤ (4 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2892, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22269 p hg
    simpa only [d2892, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2892, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22549 p hg
    simpa only [d2892, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22551 (p : Pattern) (guard : d5538 p = 1) : d2893 p ≤ (4 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2893, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22491 p hg
    simpa only [d2893, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2893, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22550 p hg
    simpa only [d2893, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22552 (p : Pattern) (guard : d5538 p = 1) : d2894 p ≤ (4 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2894, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22439 p hg
    simpa only [d2894, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2894, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22551 p hg
    simpa only [d2894, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22553 (p : Pattern) (guard : d0 p = 1) : d2507 p ≤ (0 : Int) + d321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22554 (p : Pattern) (guard : d5537 p = 1) : d2508 p ≤ (0 : Int) + d1682 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2508, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21090 p hg
    simpa only [d5537, d2508, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2508, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22553 p hg
    simpa only [d5537, d2508, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22555 (p : Pattern) (guard : d5537 p = 1) : d2511 p ≤ (0 : Int) + d1687 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2511, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21097 p hg
    simpa only [d5537, d2511, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2511, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2511, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22556 (p : Pattern) (guard : d5537 p = 1) : d2512 p ≤ (0 : Int) + d1688 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2512, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22554 p hg
    simpa only [d2512, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2512, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22555 p hg
    simpa only [d2512, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22557 (p : Pattern) (guard : d0 p = 1) : d2507 p ≤ (0 : Int) + d333 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22558 (p : Pattern) (guard : d5537 p = 1) : d2515 p ≤ (0 : Int) + d1689 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2515, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21103 p hg
    simpa only [d5537, d2515, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2515, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22557 p hg
    simpa only [d5537, d2515, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22559 (p : Pattern) (guard : d5537 p = 1) : d2516 p ≤ (0 : Int) + d1690 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2516, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22558 p hg
    simpa only [d2516, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2516, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22555 p hg
    simpa only [d2516, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22560 (p : Pattern) (guard : d5537 p = 1) : d2517 p ≤ (0 : Int) + d1691 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2517, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22556 p hg
    simpa only [d2517, d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2517, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22559 p hg
    simpa only [d2517, d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22561 (p : Pattern) (guard : d0 p = 1) : d2507 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22562 (p : Pattern) (guard : d5537 p = 1) : d2518 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2518, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d5537, d2518, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2518, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22561 p hg
    simpa only [d5537, d2518, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22563 (p : Pattern) (guard : d5537 p = 1) : d2519 p ≤ (0 : Int) + d1692 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2519, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2519, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2519, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22555 p hg
    simpa only [d2519, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22564 (p : Pattern) (guard : d0 p = 1) : d2522 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22565 (p : Pattern) (guard : d5537 p = 1) : d2523 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2523, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d5537, d2523, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2523, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22564 p hg
    simpa only [d5537, d2523, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22566 (p : Pattern) (guard : d5537 p = 1) : d2526 p ≤ (0 : Int) + d1697 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2526, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21116 p hg
    simpa only [d5537, d2526, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2526, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2526, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22567 (p : Pattern) (guard : d5537 p = 1) : d2527 p ≤ (0 : Int) + d1698 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2527, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22565 p hg
    simpa only [d2527, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2527, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22566 p hg
    simpa only [d2527, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22568 (p : Pattern) (guard : d5537 p = 1) : d2528 p ≤ (0 : Int) + d1699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2528, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22563 p hg
    simpa only [d2528, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2528, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22567 p hg
    simpa only [d2528, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22569 (p : Pattern) (guard : d5537 p = 1) : d2529 p ≤ (0 : Int) + d1700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2529, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22560 p hg
    simpa only [d2529, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2529, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22568 p hg
    simpa only [d2529, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22570 (p : Pattern) (guard : d0 p = 1) : d2531 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22571 (p : Pattern) (guard : d5537 p = 1) : d2532 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2532, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d5537, d2532, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2532, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22570 p hg
    simpa only [d5537, d2532, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22572 (p : Pattern) (guard : d5537 p = 1) : d2535 p ≤ (0 : Int) + d1705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2535, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21128 p hg
    simpa only [d5537, d2535, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2535, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2535, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22573 (p : Pattern) (guard : d5537 p = 1) : d2536 p ≤ (0 : Int) + d1706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2536, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22571 p hg
    simpa only [d2536, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2536, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22572 p hg
    simpa only [d2536, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22574 (p : Pattern) (guard : d5537 p = 1) : d2537 p ≤ (0 : Int) + d1707 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2537, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22573 p hg
    simpa only [d2537, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2537, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2537, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22575 (p : Pattern) (guard : d5537 p = 1) : d2538 p ≤ (0 : Int) + d1708 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2538, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22568 p hg
    simpa only [d2538, d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2538, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22574 p hg
    simpa only [d2538, d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22576 (p : Pattern) (guard : d5537 p = 1) : d2539 p ≤ (0 : Int) + d1709 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2539, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22569 p hg
    simpa only [d2539, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2539, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22575 p hg
    simpa only [d2539, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22577 (p : Pattern) (guard : d5537 p = 1) : d2543 p ≤ (0 : Int) + d1718 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2543, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21143 p hg
    simpa only [d5537, d2543, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2543, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2543, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22578 (p : Pattern) (guard : d5537 p = 1) : d2544 p ≤ (0 : Int) + d1719 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2544, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2544, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2544, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22577 p hg
    simpa only [d2544, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22579 (p : Pattern) (guard : d5537 p = 1) : d2548 p ≤ (0 : Int) + d1725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2548, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21148 p hg
    simpa only [d5537, d2548, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2548, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2548, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22580 (p : Pattern) (guard : d5537 p = 1) : d2549 p ≤ (0 : Int) + d1726 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2549, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2549, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2549, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22579 p hg
    simpa only [d2549, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22581 (p : Pattern) (guard : d5537 p = 1) : d2550 p ≤ (0 : Int) + d1727 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2550, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22578 p hg
    simpa only [d2550, d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2550, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22580 p hg
    simpa only [d2550, d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22582 (p : Pattern) (guard : d5537 p = 1) : d2553 p ≤ (0 : Int) + d1730 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2553, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21154 p hg
    simpa only [d5537, d2553, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2553, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2553, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22583 (p : Pattern) (guard : d5537 p = 1) : d2554 p ≤ (0 : Int) + d1731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2554, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2554, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2554, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22582 p hg
    simpa only [d2554, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22584 (p : Pattern) (guard : d5537 p = 1) : d2555 p ≤ (0 : Int) + d1732 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2555, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22565 p hg
    simpa only [d2555, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2555, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2555, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22585 (p : Pattern) (guard : d5537 p = 1) : d2556 p ≤ (0 : Int) + d1733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2556, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22583 p hg
    simpa only [d2556, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2556, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22584 p hg
    simpa only [d2556, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22586 (p : Pattern) (guard : d5537 p = 1) : d2557 p ≤ (0 : Int) + d1734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2557, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22581 p hg
    simpa only [d2557, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2557, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22585 p hg
    simpa only [d2557, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22587 (p : Pattern) (guard : d5537 p = 1) : d2558 p ≤ (0 : Int) + d1735 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2558, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2558, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2558, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2558, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22588 (p : Pattern) (guard : d5537 p = 1) : d2559 p ≤ (0 : Int) + d1736 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2559, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22587 p hg
    simpa only [d2559, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2559, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22584 p hg
    simpa only [d2559, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22589 (p : Pattern) (guard : d5537 p = 1) : d2560 p ≤ (0 : Int) + d527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2560, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22571 p hg
    simpa only [d2560, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2560, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2560, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22590 (p : Pattern) (guard : d5537 p = 1) : d2561 p ≤ (0 : Int) + d528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2561, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22589 p hg
    simpa only [d2561, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2561, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2561, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22591 (p : Pattern) (guard : d5537 p = 1) : d2562 p ≤ (0 : Int) + d1737 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2562, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22588 p hg
    simpa only [d2562, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2562, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22590 p hg
    simpa only [d2562, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22592 (p : Pattern) (guard : d5537 p = 1) : d2563 p ≤ (0 : Int) + d1738 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2563, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22586 p hg
    simpa only [d2563, d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2563, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22591 p hg
    simpa only [d2563, d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22593 (p : Pattern) (guard : d5537 p = 1) : d2564 p ≤ (0 : Int) + d1739 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2564, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22576 p hg
    simpa only [d2564, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2564, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22592 p hg
    simpa only [d2564, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22594 (p : Pattern) (guard : d0 p = 1) : d2507 p ≤ (0 : Int) + d335 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22595 (p : Pattern) (guard : d5537 p = 1) : d2567 p ≤ (0 : Int) + d1740 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2567, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21174 p hg
    simpa only [d5537, d2567, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2567, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22594 p hg
    simpa only [d5537, d2567, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22596 (p : Pattern) (guard : d5537 p = 1) : d2568 p ≤ (0 : Int) + d1741 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2568, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22595 p hg
    simpa only [d2568, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2568, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22555 p hg
    simpa only [d2568, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22597 (p : Pattern) (guard : d0 p = 1) : d2542 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22598 (p : Pattern) (guard : d5537 p = 1) : d2569 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2569, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d5537, d2569, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2569, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22597 p hg
    simpa only [d5537, d2569, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22599 (p : Pattern) (guard : d5537 p = 1) : d2572 p ≤ (0 : Int) + d1746 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2572, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21184 p hg
    simpa only [d5537, d2572, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2572, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2572, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22600 (p : Pattern) (guard : d5537 p = 1) : d2573 p ≤ (0 : Int) + d1747 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2573, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22598 p hg
    simpa only [d2573, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2573, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22599 p hg
    simpa only [d2573, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22601 (p : Pattern) (guard : d5537 p = 1) : d2574 p ≤ (0 : Int) + d1748 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2574, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22596 p hg
    simpa only [d2574, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2574, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22600 p hg
    simpa only [d2574, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22602 (p : Pattern) (guard : d5537 p = 1) : d2575 p ≤ (0 : Int) + d1749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2575, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22567 p hg
    simpa only [d2575, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2575, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22573 p hg
    simpa only [d2575, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22603 (p : Pattern) (guard : d5537 p = 1) : d2576 p ≤ (0 : Int) + d1750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2576, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22601 p hg
    simpa only [d2576, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2576, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22602 p hg
    simpa only [d2576, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22604 (p : Pattern) (guard : d0 p = 1) : d2578 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22605 (p : Pattern) (guard : d5537 p = 1) : d2579 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2579, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21190 p hg
    simpa only [d5537, d2579, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2579, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22604 p hg
    simpa only [d5537, d2579, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22606 (p : Pattern) (guard : d5537 p = 1) : d2580 p ≤ (0 : Int) + d1753 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2580, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21193 p hg
    simpa only [d5537, d2580, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2580, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2580, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22607 (p : Pattern) (guard : d5537 p = 1) : d2581 p ≤ (0 : Int) + d1754 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2581, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22605 p hg
    simpa only [d2581, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2581, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22606 p hg
    simpa only [d2581, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22608 (p : Pattern) (guard : d5537 p = 1) : d2582 p ≤ (0 : Int) + d1755 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2582, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22567 p hg
    simpa only [d2582, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2582, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22607 p hg
    simpa only [d2582, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22609 (p : Pattern) (guard : d0 p = 1) : d2552 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22610 (p : Pattern) (guard : d5537 p = 1) : d2583 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2583, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21198 p hg
    simpa only [d5537, d2583, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2583, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22609 p hg
    simpa only [d5537, d2583, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22611 (p : Pattern) (guard : d5537 p = 1) : d2584 p ≤ (0 : Int) + d1756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2584, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22610 p hg
    simpa only [d2584, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2584, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22582 p hg
    simpa only [d2584, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22612 (p : Pattern) (guard : d5537 p = 1) : d2585 p ≤ (0 : Int) + d1757 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2585, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22611 p hg
    simpa only [d2585, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2585, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2585, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22613 (p : Pattern) (guard : d5537 p = 1) : d2586 p ≤ (0 : Int) + d1758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2586, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22608 p hg
    simpa only [d2586, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2586, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22612 p hg
    simpa only [d2586, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22614 (p : Pattern) (guard : d5537 p = 1) : d2587 p ≤ (0 : Int) + d1759 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2587, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22603 p hg
    simpa only [d2587, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2587, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22613 p hg
    simpa only [d2587, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22615 (p : Pattern) (guard : d5537 p = 1) : d2588 p ≤ (0 : Int) + d1760 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2588, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22598 p hg
    simpa only [d2588, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2588, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2588, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22616 (p : Pattern) (guard : d5537 p = 1) : d2589 p ≤ (0 : Int) + d1761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2589, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22580 p hg
    simpa only [d2589, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2589, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22615 p hg
    simpa only [d2589, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22617 (p : Pattern) (guard : d5537 p = 1) : d2590 p ≤ (0 : Int) + d1762 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2590, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22584 p hg
    simpa only [d2590, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2590, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22589 p hg
    simpa only [d2590, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22618 (p : Pattern) (guard : d5537 p = 1) : d2591 p ≤ (0 : Int) + d1763 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2591, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22616 p hg
    simpa only [d2591, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2591, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22617 p hg
    simpa only [d2591, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22619 (p : Pattern) (guard : d5537 p = 1) : d2592 p ≤ (0 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2592, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22605 p hg
    simpa only [d2592, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2592, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2592, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22620 (p : Pattern) (guard : d5537 p = 1) : d2593 p ≤ (0 : Int) + d1764 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2593, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22584 p hg
    simpa only [d2593, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2593, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22619 p hg
    simpa only [d2593, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22621 (p : Pattern) (guard : d5537 p = 1) : d2594 p ≤ (0 : Int) + d538 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2594, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22610 p hg
    simpa only [d2594, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2594, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2594, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22622 (p : Pattern) (guard : d5537 p = 1) : d2595 p ≤ (0 : Int) + d539 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2595, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22621 p hg
    simpa only [d2595, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2595, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2595, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22623 (p : Pattern) (guard : d5537 p = 1) : d2596 p ≤ (0 : Int) + d1765 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2596, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22620 p hg
    simpa only [d2596, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2596, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22622 p hg
    simpa only [d2596, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22624 (p : Pattern) (guard : d5537 p = 1) : d2597 p ≤ (0 : Int) + d1766 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2597, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22618 p hg
    simpa only [d2597, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2597, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22623 p hg
    simpa only [d2597, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22625 (p : Pattern) (guard : d5537 p = 1) : d2598 p ≤ (0 : Int) + d1767 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2598, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22614 p hg
    simpa only [d2598, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2598, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22624 p hg
    simpa only [d2598, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22626 (p : Pattern) (guard : d5537 p = 1) : d2599 p ≤ (0 : Int) + d1768 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2599, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22593 p hg
    simpa only [d2599, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2599, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22625 p hg
    simpa only [d2599, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22627 (p : Pattern) (guard : d5537 p = 1) : d2600 p ≤ (0 : Int) + d1773 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2600, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21093 p hg
    simpa only [d5537, d2600, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2600, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2600, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22628 (p : Pattern) (guard : d5537 p = 1) : d2601 p ≤ (0 : Int) + d1774 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2601, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2601, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2601, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22627 p hg
    simpa only [d2601, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22629 (p : Pattern) (guard : d5537 p = 1) : d2600 p ≤ (0 : Int) + d1782 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2600, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21228 p hg
    simpa only [d5537, d2600, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2600, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2600, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22630 (p : Pattern) (guard : d5537 p = 1) : d2601 p ≤ (0 : Int) + d1783 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2601, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2601, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2601, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22629 p hg
    simpa only [d2601, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22631 (p : Pattern) (guard : d5537 p = 1) : d2601 p ≤ (0 : Int) + d1784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22628 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22630 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22632 (p : Pattern) (guard : d5537 p = 1) : d2600 p ≤ (0 : Int) + d1789 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2600, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21138 p hg
    simpa only [d5537, d2600, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2600, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2600, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22633 (p : Pattern) (guard : d5537 p = 1) : d2601 p ≤ (0 : Int) + d1790 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2601, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d2601, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2601, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22632 p hg
    simpa only [d2601, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22634 (p : Pattern) (guard : d5537 p = 1) : d2602 p ≤ (0 : Int) + d1798 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2602, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21160 p hg
    simpa only [d5537, d2602, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2602, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2602, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22635 (p : Pattern) (guard : d5537 p = 1) : d2603 p ≤ (0 : Int) + d1799 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2603, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22565 p hg
    simpa only [d2603, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2603, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22634 p hg
    simpa only [d2603, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22636 (p : Pattern) (guard : d5537 p = 1) : d2604 p ≤ (0 : Int) + d1800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2604, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22633 p hg
    simpa only [d2604, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2604, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22635 p hg
    simpa only [d2604, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22637 (p : Pattern) (guard : d5537 p = 1) : d2605 p ≤ (0 : Int) + d1801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2605, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22631 p hg
    simpa only [d2605, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2605, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22636 p hg
    simpa only [d2605, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22638 (p : Pattern) (guard : d5537 p = 1) : d2606 p ≤ (0 : Int) + d1804 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2606, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21124 p hg
    simpa only [d5537, d2606, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2606, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2606, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22639 (p : Pattern) (guard : d5537 p = 1) : d2607 p ≤ (0 : Int) + d1805 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2607, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22571 p hg
    simpa only [d2607, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2607, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22638 p hg
    simpa only [d2607, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22640 (p : Pattern) (guard : d5537 p = 1) : d2608 p ≤ (0 : Int) + d1806 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2608, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22639 p hg
    simpa only [d2608, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2608, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2608, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22641 (p : Pattern) (guard : d5537 p = 1) : d2609 p ≤ (0 : Int) + d1807 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2609, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22636 p hg
    simpa only [d2609, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2609, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22640 p hg
    simpa only [d2609, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22642 (p : Pattern) (guard : d5537 p = 1) : d2610 p ≤ (0 : Int) + d1808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2610, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22637 p hg
    simpa only [d2610, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2610, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22641 p hg
    simpa only [d2610, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22643 (p : Pattern) (guard : d5537 p = 1) : d2611 p ≤ (0 : Int) + d1809 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2611, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22598 p hg
    simpa only [d2611, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2611, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22577 p hg
    simpa only [d2611, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22644 (p : Pattern) (guard : d0 p = 1) : d2547 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22645 (p : Pattern) (guard : d5537 p = 1) : d2612 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2612, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21244 p hg
    simpa only [d5537, d2612, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2612, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22644 p hg
    simpa only [d5537, d2612, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22646 (p : Pattern) (guard : d5537 p = 1) : d2613 p ≤ (0 : Int) + d1810 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2613, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22645 p hg
    simpa only [d2613, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2613, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22579 p hg
    simpa only [d2613, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22647 (p : Pattern) (guard : d5537 p = 1) : d2614 p ≤ (0 : Int) + d1811 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2614, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22643 p hg
    simpa only [d2614, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2614, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22646 p hg
    simpa only [d2614, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22648 (p : Pattern) (guard : d5537 p = 1) : d2615 p ≤ (0 : Int) + d1812 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2615, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22647 p hg
    simpa only [d2615, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2615, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22612 p hg
    simpa only [d2615, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22649 (p : Pattern) (guard : d5537 p = 1) : d2616 p ≤ (0 : Int) + d1813 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2616, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22648 p hg
    simpa only [d2616, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2616, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2616, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22650 (p : Pattern) (guard : d5537 p = 1) : d2617 p ≤ (0 : Int) + d1814 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2617, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22642 p hg
    simpa only [d2617, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2617, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22649 p hg
    simpa only [d2617, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22651 (p : Pattern) (guard : d5537 p = 1) : d2618 p ≤ (0 : Int) + d1815 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2618, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22630 p hg
    simpa only [d2618, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2618, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22643 p hg
    simpa only [d2618, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22652 (p : Pattern) (guard : d5537 p = 1) : d2619 p ≤ (0 : Int) + d1816 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2619, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22635 p hg
    simpa only [d2619, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2619, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22639 p hg
    simpa only [d2619, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22653 (p : Pattern) (guard : d5537 p = 1) : d2620 p ≤ (0 : Int) + d1817 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2620, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22651 p hg
    simpa only [d2620, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2620, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22652 p hg
    simpa only [d2620, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22654 (p : Pattern) (guard : d5537 p = 1) : d2621 p ≤ (0 : Int) + d1818 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2621, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22635 p hg
    simpa only [d2621, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2621, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22607 p hg
    simpa only [d2621, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22655 (p : Pattern) (guard : d5537 p = 1) : d2622 p ≤ (0 : Int) + d1819 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2622, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22654 p hg
    simpa only [d2622, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2622, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22612 p hg
    simpa only [d2622, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22656 (p : Pattern) (guard : d5537 p = 1) : d2623 p ≤ (0 : Int) + d1820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2623, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22653 p hg
    simpa only [d2623, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2623, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22655 p hg
    simpa only [d2623, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22657 (p : Pattern) (guard : d5537 p = 1) : d2624 p ≤ (0 : Int) + d1821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2624, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22646 p hg
    simpa only [d2624, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2624, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2624, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22658 (p : Pattern) (guard : d5537 p = 1) : d2625 p ≤ (0 : Int) + d1822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2625, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22657 p hg
    simpa only [d2625, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2625, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2625, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22659 (p : Pattern) (guard : d5537 p = 1) : d2626 p ≤ (0 : Int) + d1823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2626, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22658 p hg
    simpa only [d2626, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2626, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2626, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22660 (p : Pattern) (guard : d5537 p = 1) : d2627 p ≤ (0 : Int) + d1824 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2627, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22656 p hg
    simpa only [d2627, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2627, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22659 p hg
    simpa only [d2627, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22661 (p : Pattern) (guard : d5537 p = 1) : d2628 p ≤ (0 : Int) + d1825 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2628, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22650 p hg
    simpa only [d2628, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2628, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22660 p hg
    simpa only [d2628, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22662 (p : Pattern) (guard : d5537 p = 1) : d2629 p ≤ (0 : Int) + d1826 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2629, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22626 p hg
    simpa only [d2629, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2629, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22661 p hg
    simpa only [d2629, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22663 (p : Pattern) (guard : d5537 p = 1) : d2630 p ≤ (0 : Int) + d1827 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2630, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22639 p hg
    simpa only [d2630, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2630, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22611 p hg
    simpa only [d2630, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22664 (p : Pattern) (guard : d5537 p = 1) : d2631 p ≤ (0 : Int) + d1828 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2631, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22663 p hg
    simpa only [d2631, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2631, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22612 p hg
    simpa only [d2631, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22665 (p : Pattern) (guard : d5537 p = 1) : d2632 p ≤ (0 : Int) + d1829 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2632, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22612 p hg
    simpa only [d2632, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2632, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2632, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22666 (p : Pattern) (guard : d5537 p = 1) : d2633 p ≤ (0 : Int) + d1830 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2633, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22664 p hg
    simpa only [d2633, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2633, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22665 p hg
    simpa only [d2633, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22667 (p : Pattern) (guard : d5537 p = 1) : d2634 p ≤ (0 : Int) + d1831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2634, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22665 p hg
    simpa only [d2634, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2634, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2634, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22668 (p : Pattern) (guard : d5537 p = 1) : d2635 p ≤ (0 : Int) + d1832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2635, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22666 p hg
    simpa only [d2635, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2635, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22667 p hg
    simpa only [d2635, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22669 (p : Pattern) (guard : d5537 p = 1) : d2636 p ≤ (0 : Int) + d1833 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2636, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22667 p hg
    simpa only [d2636, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2636, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2636, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22670 (p : Pattern) (guard : d5537 p = 1) : d2637 p ≤ (0 : Int) + d1834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2637, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22668 p hg
    simpa only [d2637, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2637, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22669 p hg
    simpa only [d2637, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22671 (p : Pattern) (guard : d5537 p = 1) : d2638 p ≤ (0 : Int) + d1835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2638, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22661 p hg
    simpa only [d2638, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2638, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22670 p hg
    simpa only [d2638, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22672 (p : Pattern) (guard : d5537 p = 1) : d2639 p ≤ (0 : Int) + d1836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2639, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22662 p hg
    simpa only [d2639, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2639, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22671 p hg
    simpa only [d2639, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22673 (p : Pattern) (guard : d5537 p = 1) : d2640 p ≤ (0 : Int) + d1837 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2640, d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22559 p hg
    simpa only [d2640, d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2640, d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22563 p hg
    simpa only [d2640, d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22674 (p : Pattern) (guard : d5537 p = 1) : d2641 p ≤ (0 : Int) + d1838 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2641, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22673 p hg
    simpa only [d2641, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2641, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22568 p hg
    simpa only [d2641, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22675 (p : Pattern) (guard : d5537 p = 1) : d2642 p ≤ (0 : Int) + d1839 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2642, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22674 p hg
    simpa only [d2642, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2642, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22575 p hg
    simpa only [d2642, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22676 (p : Pattern) (guard : d5537 p = 1) : d2643 p ≤ (0 : Int) + d1840 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2643, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22675 p hg
    simpa only [d2643, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2643, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22592 p hg
    simpa only [d2643, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22677 (p : Pattern) (guard : d5537 p = 1) : d2644 p ≤ (0 : Int) + d1841 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2644, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22563 p hg
    simpa only [d2644, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2644, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22600 p hg
    simpa only [d2644, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22678 (p : Pattern) (guard : d5537 p = 1) : d2645 p ≤ (0 : Int) + d1842 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2645, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22677 p hg
    simpa only [d2645, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2645, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22602 p hg
    simpa only [d2645, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22679 (p : Pattern) (guard : d5537 p = 1) : d2646 p ≤ (0 : Int) + d1843 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2646, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22678 p hg
    simpa only [d2646, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2646, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22613 p hg
    simpa only [d2646, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
