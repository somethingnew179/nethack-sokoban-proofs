/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons121
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17080 (p : Pattern) (guard : d4967 p = 1) : d2183 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2183, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16947 p hg
    simpa only [d2183, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2183, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17079 p hg
    simpa only [d2183, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17081 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2505 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14832 p hg
    simpa only [d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17082 (p : Pattern) (guard : d0 p = 1) : d321 p ≤ (0 : Int) + d2507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17083 (p : Pattern) (guard : d5537 p = 1) : d1682 p ≤ (0 : Int) + d2508 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1682, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17081 p hg
    simpa only [d5537, d1682, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1682, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17082 p hg
    simpa only [d5537, d1682, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17084 (p : Pattern) (guard : d0 p = 1) : d1684 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17085 (p : Pattern) (guard : d5502 p = 1) : d1685 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1685, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d1685, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1685, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17084 p hg
    simpa only [d5502, d1685, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17086 (p : Pattern) (guard : d1 p = 1) : d1684 p ≤ (0 : Int) + d1684 p := by
  omega
theorem compare17087 (p : Pattern) (guard : d5502 p = 1) : d1684 p ≤ (0 : Int) + d2509 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17086 p hg
    simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17084 p hg
    simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17088 (p : Pattern) (guard : d5502 p = 1) : d1686 p ≤ (0 : Int) + d2510 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1686, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17085 p hg
    simpa only [d1686, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1686, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17087 p hg
    simpa only [d1686, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17089 (p : Pattern) (guard : d5537 p = 1) : d1687 p ≤ (0 : Int) + d2511 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1687, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17088 p hg
    simpa only [d5537, d1687, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1687, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1687, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17090 (p : Pattern) (guard : d5537 p = 1) : d1688 p ≤ (0 : Int) + d2512 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1688, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17083 p hg
    simpa only [d1688, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1688, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17089 p hg
    simpa only [d1688, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17091 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2514 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14845 p hg
    simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17092 (p : Pattern) (guard : d0 p = 1) : d333 p ≤ (0 : Int) + d2507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17093 (p : Pattern) (guard : d5537 p = 1) : d1689 p ≤ (0 : Int) + d2515 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1689, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17091 p hg
    simpa only [d5537, d1689, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1689, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17092 p hg
    simpa only [d5537, d1689, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17094 (p : Pattern) (guard : d5537 p = 1) : d1690 p ≤ (0 : Int) + d2516 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1690, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17093 p hg
    simpa only [d1690, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1690, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17089 p hg
    simpa only [d1690, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17095 (p : Pattern) (guard : d5537 p = 1) : d1691 p ≤ (0 : Int) + d2517 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1691, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17090 p hg
    simpa only [d1691, d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1691, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17094 p hg
    simpa only [d1691, d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17096 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17097 (p : Pattern) (guard : d5537 p = 1) : d15 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d15, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d5537, d15, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d15, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17096 p hg
    simpa only [d5537, d15, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17098 (p : Pattern) (guard : d5537 p = 1) : d1692 p ≤ (0 : Int) + d2519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1692, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d1692, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1692, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17089 p hg
    simpa only [d1692, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17099 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2522 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17100 (p : Pattern) (guard : d5537 p = 1) : d19 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d19, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d5537, d19, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d19, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17099 p hg
    simpa only [d5537, d19, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17101 (p : Pattern) (guard : d0 p = 1) : d1694 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17102 (p : Pattern) (guard : d5502 p = 1) : d1695 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1695, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d5502, d1695, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1695, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17101 p hg
    simpa only [d5502, d1695, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17103 (p : Pattern) (guard : d1 p = 1) : d1694 p ≤ (0 : Int) + d1694 p := by
  omega
theorem compare17104 (p : Pattern) (guard : d5502 p = 1) : d1694 p ≤ (0 : Int) + d2524 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17103 p hg
    simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17101 p hg
    simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17105 (p : Pattern) (guard : d5502 p = 1) : d1696 p ≤ (0 : Int) + d2525 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1696, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17102 p hg
    simpa only [d1696, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1696, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17104 p hg
    simpa only [d1696, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17106 (p : Pattern) (guard : d5537 p = 1) : d1697 p ≤ (0 : Int) + d2526 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1697, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17105 p hg
    simpa only [d5537, d1697, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1697, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1697, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17107 (p : Pattern) (guard : d5537 p = 1) : d1698 p ≤ (0 : Int) + d2527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1698, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17100 p hg
    simpa only [d1698, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1698, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17106 p hg
    simpa only [d1698, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17108 (p : Pattern) (guard : d5537 p = 1) : d1699 p ≤ (0 : Int) + d2528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1699, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17098 p hg
    simpa only [d1699, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1699, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17107 p hg
    simpa only [d1699, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17109 (p : Pattern) (guard : d5537 p = 1) : d1700 p ≤ (0 : Int) + d2529 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1700, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17095 p hg
    simpa only [d1700, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1700, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17108 p hg
    simpa only [d1700, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17110 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2531 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17111 (p : Pattern) (guard : d5537 p = 1) : d25 p ≤ (0 : Int) + d2532 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d25, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d5537, d25, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d25, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17110 p hg
    simpa only [d5537, d25, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17112 (p : Pattern) (guard : d0 p = 1) : d1702 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17113 (p : Pattern) (guard : d5502 p = 1) : d1703 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1703, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d5502, d1703, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1703, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17112 p hg
    simpa only [d5502, d1703, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17114 (p : Pattern) (guard : d1 p = 1) : d1702 p ≤ (0 : Int) + d1702 p := by
  omega
theorem compare17115 (p : Pattern) (guard : d5502 p = 1) : d1702 p ≤ (0 : Int) + d2533 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17114 p hg
    simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17112 p hg
    simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17116 (p : Pattern) (guard : d5502 p = 1) : d1704 p ≤ (0 : Int) + d2534 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1704, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17113 p hg
    simpa only [d1704, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1704, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17115 p hg
    simpa only [d1704, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17117 (p : Pattern) (guard : d5537 p = 1) : d1705 p ≤ (0 : Int) + d2535 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1705, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17116 p hg
    simpa only [d5537, d1705, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1705, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1705, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17118 (p : Pattern) (guard : d5537 p = 1) : d1706 p ≤ (0 : Int) + d2536 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1706, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17111 p hg
    simpa only [d1706, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1706, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17117 p hg
    simpa only [d1706, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17119 (p : Pattern) (guard : d5537 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare17120 (p : Pattern) (guard : d5537 p = 1) : d1707 p ≤ (0 : Int) + d2537 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1707, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17118 p hg
    simpa only [d1707, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1707, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1707, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17121 (p : Pattern) (guard : d5537 p = 1) : d1708 p ≤ (0 : Int) + d2538 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1708, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17108 p hg
    simpa only [d1708, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1708, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17120 p hg
    simpa only [d1708, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17122 (p : Pattern) (guard : d5537 p = 1) : d1709 p ≤ (0 : Int) + d2539 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1709, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17109 p hg
    simpa only [d1709, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1709, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17121 p hg
    simpa only [d1709, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17123 (p : Pattern) (guard : d0 p = 1) : d1711 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17124 (p : Pattern) (guard : d5502 p = 1) : d1712 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1712, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d5502, d1712, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1712, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17123 p hg
    simpa only [d5502, d1712, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17125 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (0 : Int) + d1714 p := by
  omega
theorem compare17126 (p : Pattern) (guard : d0 p = 1) : d1715 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17127 (p : Pattern) (guard : d5502 p = 1) : d1716 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1716, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d5502, d1716, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1716, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17126 p hg
    simpa only [d5502, d1716, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17128 (p : Pattern) (guard : d5502 p = 1) : d1717 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1717, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17124 p hg
    simpa only [d1717, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1717, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17127 p hg
    simpa only [d1717, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17129 (p : Pattern) (guard : d5537 p = 1) : d1718 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1718, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17128 p hg
    simpa only [d5537, d1718, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1718, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1718, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17130 (p : Pattern) (guard : d5537 p = 1) : d1719 p ≤ (0 : Int) + d2544 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1719, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d1719, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1719, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17129 p hg
    simpa only [d1719, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17131 (p : Pattern) (guard : d0 p = 1) : d364 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17132 (p : Pattern) (guard : d5502 p = 1) : d1720 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1720, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d5502, d1720, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1720, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d5502, d1720, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17133 (p : Pattern) (guard : d1 p = 1) : d1722 p ≤ (0 : Int) + d1722 p := by
  omega
theorem compare17134 (p : Pattern) (guard : d5502 p = 1) : d1723 p ≤ (0 : Int) + d2546 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1723, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17133 p hg
    simpa only [d5502, d1723, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1723, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d5502, d1723, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17135 (p : Pattern) (guard : d5502 p = 1) : d1724 p ≤ (0 : Int) + d2547 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1724, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17132 p hg
    simpa only [d1724, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1724, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17134 p hg
    simpa only [d1724, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17136 (p : Pattern) (guard : d5537 p = 1) : d1725 p ≤ (0 : Int) + d2548 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1725, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17135 p hg
    simpa only [d5537, d1725, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1725, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1725, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17137 (p : Pattern) (guard : d5537 p = 1) : d1726 p ≤ (0 : Int) + d2549 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1726, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d1726, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1726, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17136 p hg
    simpa only [d1726, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17138 (p : Pattern) (guard : d5537 p = 1) : d1727 p ≤ (0 : Int) + d2550 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1727, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17130 p hg
    simpa only [d1727, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1727, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17137 p hg
    simpa only [d1727, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17139 (p : Pattern) (guard : d0 p = 1) : d327 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17140 (p : Pattern) (guard : d5502 p = 1) : d1728 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1728, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d5502, d1728, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1728, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d5502, d1728, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17141 (p : Pattern) (guard : d1 p = 1) : d327 p ≤ (0 : Int) + d327 p := by
  omega
theorem compare17142 (p : Pattern) (guard : d5502 p = 1) : d327 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17141 p hg
    simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17143 (p : Pattern) (guard : d5502 p = 1) : d1729 p ≤ (0 : Int) + d2552 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1729, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17140 p hg
    simpa only [d1729, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1729, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17142 p hg
    simpa only [d1729, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17144 (p : Pattern) (guard : d5537 p = 1) : d1730 p ≤ (0 : Int) + d2553 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1730, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17143 p hg
    simpa only [d5537, d1730, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1730, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1730, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17145 (p : Pattern) (guard : d5537 p = 1) : d1731 p ≤ (0 : Int) + d2554 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1731, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d1731, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1731, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17144 p hg
    simpa only [d1731, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17146 (p : Pattern) (guard : d5537 p = 1) : d1732 p ≤ (0 : Int) + d2555 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1732, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17100 p hg
    simpa only [d1732, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1732, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1732, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17147 (p : Pattern) (guard : d5537 p = 1) : d1733 p ≤ (0 : Int) + d2556 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1733, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17145 p hg
    simpa only [d1733, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1733, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17146 p hg
    simpa only [d1733, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17148 (p : Pattern) (guard : d5537 p = 1) : d1734 p ≤ (0 : Int) + d2557 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1734, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17138 p hg
    simpa only [d1734, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1734, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17147 p hg
    simpa only [d1734, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17149 (p : Pattern) (guard : d5537 p = 1) : d1735 p ≤ (0 : Int) + d2558 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1735, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d1735, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1735, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1735, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17150 (p : Pattern) (guard : d5537 p = 1) : d1736 p ≤ (0 : Int) + d2559 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1736, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17149 p hg
    simpa only [d1736, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1736, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17146 p hg
    simpa only [d1736, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17151 (p : Pattern) (guard : d5537 p = 1) : d527 p ≤ (0 : Int) + d2560 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d527, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17111 p hg
    simpa only [d527, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d527, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d527, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17152 (p : Pattern) (guard : d5537 p = 1) : d528 p ≤ (0 : Int) + d2561 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d528, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17151 p hg
    simpa only [d528, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d528, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d528, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17153 (p : Pattern) (guard : d5537 p = 1) : d1737 p ≤ (0 : Int) + d2562 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1737, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17150 p hg
    simpa only [d1737, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1737, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17152 p hg
    simpa only [d1737, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17154 (p : Pattern) (guard : d5537 p = 1) : d1738 p ≤ (0 : Int) + d2563 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1738, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17148 p hg
    simpa only [d1738, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1738, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17153 p hg
    simpa only [d1738, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17155 (p : Pattern) (guard : d5537 p = 1) : d1739 p ≤ (0 : Int) + d2564 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1739, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17122 p hg
    simpa only [d1739, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1739, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17154 p hg
    simpa only [d1739, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17156 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2566 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14905 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17157 (p : Pattern) (guard : d0 p = 1) : d335 p ≤ (0 : Int) + d2507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17158 (p : Pattern) (guard : d5537 p = 1) : d1740 p ≤ (0 : Int) + d2567 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1740, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17156 p hg
    simpa only [d5537, d1740, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1740, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17157 p hg
    simpa only [d5537, d1740, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17159 (p : Pattern) (guard : d5537 p = 1) : d1741 p ≤ (0 : Int) + d2568 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1741, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17158 p hg
    simpa only [d1741, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1741, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17089 p hg
    simpa only [d1741, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17160 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2542 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17161 (p : Pattern) (guard : d5537 p = 1) : d32 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d32, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d5537, d32, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d32, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17160 p hg
    simpa only [d5537, d32, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17162 (p : Pattern) (guard : d0 p = 1) : d1743 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17163 (p : Pattern) (guard : d5502 p = 1) : d1744 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1744, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d5502, d1744, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1744, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17162 p hg
    simpa only [d5502, d1744, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17164 (p : Pattern) (guard : d1 p = 1) : d1743 p ≤ (0 : Int) + d1743 p := by
  omega
theorem compare17165 (p : Pattern) (guard : d5502 p = 1) : d1743 p ≤ (0 : Int) + d2570 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17164 p hg
    simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17162 p hg
    simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17166 (p : Pattern) (guard : d5502 p = 1) : d1745 p ≤ (0 : Int) + d2571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1745, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17163 p hg
    simpa only [d1745, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1745, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17165 p hg
    simpa only [d1745, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17167 (p : Pattern) (guard : d5537 p = 1) : d1746 p ≤ (0 : Int) + d2572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1746, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17166 p hg
    simpa only [d5537, d1746, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1746, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1746, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17168 (p : Pattern) (guard : d5537 p = 1) : d1747 p ≤ (0 : Int) + d2573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1747, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d1747, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1747, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17167 p hg
    simpa only [d1747, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17169 (p : Pattern) (guard : d5537 p = 1) : d1748 p ≤ (0 : Int) + d2574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1748, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17159 p hg
    simpa only [d1748, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1748, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17168 p hg
    simpa only [d1748, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17170 (p : Pattern) (guard : d5537 p = 1) : d1749 p ≤ (0 : Int) + d2575 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1749, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17107 p hg
    simpa only [d1749, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1749, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17118 p hg
    simpa only [d1749, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17171 (p : Pattern) (guard : d5537 p = 1) : d1750 p ≤ (0 : Int) + d2576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1750, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17169 p hg
    simpa only [d1750, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1750, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17170 p hg
    simpa only [d1750, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17172 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2578 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17173 (p : Pattern) (guard : d5537 p = 1) : d59 p ≤ (0 : Int) + d2579 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d59, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14919 p hg
    simpa only [d5537, d59, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d59, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17172 p hg
    simpa only [d5537, d59, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17174 (p : Pattern) (guard : d0 p = 1) : d329 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17175 (p : Pattern) (guard : d5502 p = 1) : d1751 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1751, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d5502, d1751, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1751, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d5502, d1751, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17176 (p : Pattern) (guard : d1 p = 1) : d329 p ≤ (0 : Int) + d329 p := by
  omega
theorem compare17177 (p : Pattern) (guard : d5502 p = 1) : d329 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17176 p hg
    simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17178 (p : Pattern) (guard : d5502 p = 1) : d1752 p ≤ (0 : Int) + d2578 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1752, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17175 p hg
    simpa only [d1752, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1752, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17177 p hg
    simpa only [d1752, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17179 (p : Pattern) (guard : d5537 p = 1) : d1753 p ≤ (0 : Int) + d2580 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1753, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17178 p hg
    simpa only [d5537, d1753, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1753, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1753, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17180 (p : Pattern) (guard : d5537 p = 1) : d1754 p ≤ (0 : Int) + d2581 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1754, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17173 p hg
    simpa only [d1754, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1754, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17179 p hg
    simpa only [d1754, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17181 (p : Pattern) (guard : d5537 p = 1) : d1755 p ≤ (0 : Int) + d2582 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1755, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17107 p hg
    simpa only [d1755, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1755, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17180 p hg
    simpa only [d1755, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17182 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2552 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17183 (p : Pattern) (guard : d5537 p = 1) : d41 p ≤ (0 : Int) + d2583 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d41, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14889 p hg
    simpa only [d5537, d41, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d41, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17182 p hg
    simpa only [d5537, d41, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17184 (p : Pattern) (guard : d5537 p = 1) : d1756 p ≤ (0 : Int) + d2584 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1756, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17183 p hg
    simpa only [d1756, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1756, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17144 p hg
    simpa only [d1756, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17185 (p : Pattern) (guard : d5537 p = 1) : d1757 p ≤ (0 : Int) + d2585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1757, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17184 p hg
    simpa only [d1757, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1757, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1757, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17186 (p : Pattern) (guard : d5537 p = 1) : d1758 p ≤ (0 : Int) + d2586 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1758, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17181 p hg
    simpa only [d1758, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1758, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17185 p hg
    simpa only [d1758, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17187 (p : Pattern) (guard : d5537 p = 1) : d1759 p ≤ (0 : Int) + d2587 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1759, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17171 p hg
    simpa only [d1759, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1759, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17186 p hg
    simpa only [d1759, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17188 (p : Pattern) (guard : d5537 p = 1) : d1760 p ≤ (0 : Int) + d2588 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1760, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d1760, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1760, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1760, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17189 (p : Pattern) (guard : d5537 p = 1) : d1761 p ≤ (0 : Int) + d2589 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1761, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17137 p hg
    simpa only [d1761, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1761, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17188 p hg
    simpa only [d1761, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17190 (p : Pattern) (guard : d5537 p = 1) : d1762 p ≤ (0 : Int) + d2590 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1762, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17146 p hg
    simpa only [d1762, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1762, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17151 p hg
    simpa only [d1762, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17191 (p : Pattern) (guard : d5537 p = 1) : d1763 p ≤ (0 : Int) + d2591 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1763, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17189 p hg
    simpa only [d1763, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1763, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17190 p hg
    simpa only [d1763, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17192 (p : Pattern) (guard : d5537 p = 1) : d277 p ≤ (0 : Int) + d2592 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d277, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17173 p hg
    simpa only [d277, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d277, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d277, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17193 (p : Pattern) (guard : d5537 p = 1) : d1764 p ≤ (0 : Int) + d2593 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1764, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17146 p hg
    simpa only [d1764, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1764, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17192 p hg
    simpa only [d1764, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17194 (p : Pattern) (guard : d5537 p = 1) : d538 p ≤ (0 : Int) + d2594 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d538, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17183 p hg
    simpa only [d538, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d538, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d538, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17195 (p : Pattern) (guard : d5537 p = 1) : d539 p ≤ (0 : Int) + d2595 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d539, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17194 p hg
    simpa only [d539, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d539, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d539, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17196 (p : Pattern) (guard : d5537 p = 1) : d1765 p ≤ (0 : Int) + d2596 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1765, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17193 p hg
    simpa only [d1765, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1765, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17195 p hg
    simpa only [d1765, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17197 (p : Pattern) (guard : d5537 p = 1) : d1766 p ≤ (0 : Int) + d2597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1766, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17191 p hg
    simpa only [d1766, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1766, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17196 p hg
    simpa only [d1766, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17198 (p : Pattern) (guard : d5537 p = 1) : d1767 p ≤ (0 : Int) + d2598 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1767, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17187 p hg
    simpa only [d1767, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1767, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17197 p hg
    simpa only [d1767, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17199 (p : Pattern) (guard : d5537 p = 1) : d1768 p ≤ (0 : Int) + d2599 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1768, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17155 p hg
    simpa only [d1768, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1768, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17198 p hg
    simpa only [d1768, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17200 (p : Pattern) (guard : d0 p = 1) : d1770 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17201 (p : Pattern) (guard : d5502 p = 1) : d1771 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1771, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d1771, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1771, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17200 p hg
    simpa only [d5502, d1771, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17202 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (0 : Int) + d1770 p := by
  omega
theorem compare17203 (p : Pattern) (guard : d5502 p = 1) : d1770 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17200 p hg
    simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17204 (p : Pattern) (guard : d5502 p = 1) : d1772 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1772, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17201 p hg
    simpa only [d1772, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1772, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17203 p hg
    simpa only [d1772, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17205 (p : Pattern) (guard : d5537 p = 1) : d1773 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1773, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d5537, d1773, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1773, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1773, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17206 (p : Pattern) (guard : d5537 p = 1) : d1774 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1774, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d1774, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1774, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17205 p hg
    simpa only [d1774, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17207 (p : Pattern) (guard : d0 p = 1) : d1776 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17208 (p : Pattern) (guard : d5502 p = 1) : d1777 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1777, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d1777, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1777, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17207 p hg
    simpa only [d5502, d1777, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17209 (p : Pattern) (guard : d0 p = 1) : d1779 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17210 (p : Pattern) (guard : d5502 p = 1) : d1780 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1780, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d1780, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1780, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17209 p hg
    simpa only [d5502, d1780, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17211 (p : Pattern) (guard : d5502 p = 1) : d1781 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1781, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17208 p hg
    simpa only [d1781, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1781, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17210 p hg
    simpa only [d1781, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17212 (p : Pattern) (guard : d5537 p = 1) : d1782 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1782, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17211 p hg
    simpa only [d5537, d1782, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1782, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1782, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17213 (p : Pattern) (guard : d5537 p = 1) : d1783 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1783, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d1783, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1783, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17212 p hg
    simpa only [d1783, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17214 (p : Pattern) (guard : d5537 p = 1) : d1784 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17206 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17213 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17215 (p : Pattern) (guard : d0 p = 1) : d1786 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17216 (p : Pattern) (guard : d5502 p = 1) : d1787 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1787, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d1787, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1787, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17215 p hg
    simpa only [d5502, d1787, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17217 (p : Pattern) (guard : d5502 p = 1) : d1788 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1788, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17208 p hg
    simpa only [d1788, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1788, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17216 p hg
    simpa only [d1788, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17218 (p : Pattern) (guard : d5537 p = 1) : d1789 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1789, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17217 p hg
    simpa only [d5537, d1789, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1789, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1789, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17219 (p : Pattern) (guard : d5537 p = 1) : d1790 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1790, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d1790, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1790, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17218 p hg
    simpa only [d1790, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
