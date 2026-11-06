/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22120 (p : Pattern) (guard : d1 p = 1) : d1702 p ≤ (4 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1702, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22119 p hg
    simpa only [d1702, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1702, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2654 p hg
    simpa only [d1702, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22121 (p : Pattern) (guard : d5502 p = 1) : d2533 p ≤ (4 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22120 p hg
    simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22110 p hg
    simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22122 (p : Pattern) (guard : d5538 p = 1) : d2534 p ≤ (4 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22109 p hg
    simpa only [d5538, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22121 p hg
    simpa only [d5538, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22123 (p : Pattern) (guard : d5538 p = 1) : d2535 p ≤ (4 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2535, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22122 p hg
    simpa only [d2535, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2535, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2535, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22124 (p : Pattern) (guard : d5538 p = 1) : d2536 p ≤ (4 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2536, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22118 p hg
    simpa only [d2536, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2536, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22123 p hg
    simpa only [d2536, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22125 (p : Pattern) (guard : d5538 p = 1) : d2537 p ≤ (4 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2537, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22124 p hg
    simpa only [d2537, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2537, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2537, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22126 (p : Pattern) (guard : d5538 p = 1) : d2538 p ≤ (4 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2538, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22107 p hg
    simpa only [d2538, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2538, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22125 p hg
    simpa only [d2538, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22127 (p : Pattern) (guard : d5538 p = 1) : d2539 p ≤ (4 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2539, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22108 p hg
    simpa only [d2539, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2539, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22126 p hg
    simpa only [d2539, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22128 (p : Pattern) (guard : d0 p = 1) : d2540 p ≤ (4 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22129 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (4 : Int) + d2 p := by
  omega
theorem compare22130 (p : Pattern) (guard : d1 p = 1) : d1713 p ≤ (4 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22129 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22131 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (4 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1714, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22130 p hg
    simpa only [d1714, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1714, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2514 p hg
    simpa only [d1714, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22132 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22133 (p : Pattern) (guard : d5502 p = 1) : d2541 p ≤ (4 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22131 p hg
    simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22132 p hg
    simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22134 (p : Pattern) (guard : d5538 p = 1) : d2542 p ≤ (4 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22128 p hg
    simpa only [d5538, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22133 p hg
    simpa only [d5538, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22135 (p : Pattern) (guard : d5538 p = 1) : d2543 p ≤ (4 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2543, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22134 p hg
    simpa only [d2543, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2543, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2543, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22136 (p : Pattern) (guard : d5538 p = 1) : d2544 p ≤ (4 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2544, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22089 p hg
    simpa only [d2544, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2544, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22135 p hg
    simpa only [d2544, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22137 (p : Pattern) (guard : d0 p = 1) : d2545 p ≤ (4 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22138 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (4 : Int) + d6 p := by
  omega
theorem compare22139 (p : Pattern) (guard : d1 p = 1) : d1721 p ≤ (4 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22138 p hg
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2518 p hg
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22140 (p : Pattern) (guard : d1 p = 1) : d1722 p ≤ (4 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1722, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22139 p hg
    simpa only [d1722, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1722, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2519 p hg
    simpa only [d1722, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22141 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22142 (p : Pattern) (guard : d5502 p = 1) : d2546 p ≤ (4 : Int) + d35 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22140 p hg
    simpa only [d5502, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22141 p hg
    simpa only [d5502, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22143 (p : Pattern) (guard : d5538 p = 1) : d2547 p ≤ (4 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22137 p hg
    simpa only [d5538, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22142 p hg
    simpa only [d5538, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22144 (p : Pattern) (guard : d5538 p = 1) : d2548 p ≤ (4 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2548, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22143 p hg
    simpa only [d2548, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2548, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2548, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22145 (p : Pattern) (guard : d5538 p = 1) : d2549 p ≤ (4 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2549, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22089 p hg
    simpa only [d2549, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2549, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22144 p hg
    simpa only [d2549, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22146 (p : Pattern) (guard : d5538 p = 1) : d2550 p ≤ (4 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2550, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22136 p hg
    simpa only [d2550, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2550, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22145 p hg
    simpa only [d2550, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22147 (p : Pattern) (guard : d0 p = 1) : d2551 p ≤ (4 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22148 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (4 : Int) + d11 p := by
  omega
theorem compare22149 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (4 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22148 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2524 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22150 (p : Pattern) (guard : d1 p = 1) : d327 p ≤ (4 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22149 p hg
    simpa only [d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2525 p hg
    simpa only [d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22151 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22152 (p : Pattern) (guard : d5502 p = 1) : d332 p ≤ (4 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22150 p hg
    simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22151 p hg
    simpa only [d5502, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22153 (p : Pattern) (guard : d5538 p = 1) : d2552 p ≤ (4 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22147 p hg
    simpa only [d5538, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22152 p hg
    simpa only [d5538, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22154 (p : Pattern) (guard : d5538 p = 1) : d2553 p ≤ (4 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2553, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22153 p hg
    simpa only [d2553, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2553, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2553, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22155 (p : Pattern) (guard : d5538 p = 1) : d2554 p ≤ (4 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2554, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22089 p hg
    simpa only [d2554, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2554, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22154 p hg
    simpa only [d2554, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22156 (p : Pattern) (guard : d5538 p = 1) : d2555 p ≤ (4 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2555, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22100 p hg
    simpa only [d2555, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2555, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2555, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22157 (p : Pattern) (guard : d5538 p = 1) : d2556 p ≤ (4 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2556, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22155 p hg
    simpa only [d2556, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2556, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22156 p hg
    simpa only [d2556, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22158 (p : Pattern) (guard : d5538 p = 1) : d2557 p ≤ (4 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2557, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22146 p hg
    simpa only [d2557, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2557, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22157 p hg
    simpa only [d2557, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22159 (p : Pattern) (guard : d5538 p = 1) : d2558 p ≤ (4 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2558, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22089 p hg
    simpa only [d2558, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2558, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2558, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22160 (p : Pattern) (guard : d5538 p = 1) : d2559 p ≤ (4 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2559, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22159 p hg
    simpa only [d2559, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2559, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22156 p hg
    simpa only [d2559, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22161 (p : Pattern) (guard : d5538 p = 1) : d2560 p ≤ (4 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2560, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22118 p hg
    simpa only [d2560, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2560, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2560, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22162 (p : Pattern) (guard : d5538 p = 1) : d2561 p ≤ (4 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2561, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22161 p hg
    simpa only [d2561, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2561, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2561, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22163 (p : Pattern) (guard : d5538 p = 1) : d2562 p ≤ (4 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2562, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22160 p hg
    simpa only [d2562, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2562, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22162 p hg
    simpa only [d2562, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22164 (p : Pattern) (guard : d5538 p = 1) : d2563 p ≤ (4 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2563, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22158 p hg
    simpa only [d2563, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2563, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22163 p hg
    simpa only [d2563, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22165 (p : Pattern) (guard : d5538 p = 1) : d2564 p ≤ (4 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2564, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22127 p hg
    simpa only [d2564, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2564, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22164 p hg
    simpa only [d2564, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22166 (p : Pattern) (guard : d0 p = 1) : d2565 p ≤ (4 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22167 (p : Pattern) (guard : d5538 p = 1) : d2566 p ≤ (4 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22166 p hg
    simpa only [d5538, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22067 p hg
    simpa only [d5538, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22168 (p : Pattern) (guard : d5538 p = 1) : d2567 p ≤ (4 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22167 p hg
    simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22074 p hg
    simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22169 (p : Pattern) (guard : d5538 p = 1) : d2568 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2568, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22168 p hg
    simpa only [d2568, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2568, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22081 p hg
    simpa only [d2568, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22170 (p : Pattern) (guard : d5502 p = 1) : d2540 p ≤ (4 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22132 p hg
    simpa only [d5502, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22171 (p : Pattern) (guard : d5538 p = 1) : d2540 p ≤ (4 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22128 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22170 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22172 (p : Pattern) (guard : d5538 p = 1) : d2569 p ≤ (4 : Int) + d31 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22171 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22134 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22173 (p : Pattern) (guard : d1 p = 1) : d1742 p ≤ (4 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22129 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8381 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22174 (p : Pattern) (guard : d1 p = 1) : d1743 p ≤ (4 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1743, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22173 p hg
    simpa only [d1743, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1743, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8382 p hg
    simpa only [d1743, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22175 (p : Pattern) (guard : d5502 p = 1) : d2570 p ≤ (4 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22174 p hg
    simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22132 p hg
    simpa only [d5502, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22176 (p : Pattern) (guard : d5538 p = 1) : d2571 p ≤ (4 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22128 p hg
    simpa only [d5538, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22175 p hg
    simpa only [d5538, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22177 (p : Pattern) (guard : d5538 p = 1) : d2572 p ≤ (4 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2572, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22176 p hg
    simpa only [d2572, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2572, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2572, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22178 (p : Pattern) (guard : d5538 p = 1) : d2573 p ≤ (4 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2573, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22172 p hg
    simpa only [d2573, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2573, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22177 p hg
    simpa only [d2573, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22179 (p : Pattern) (guard : d5538 p = 1) : d2574 p ≤ (4 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2574, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22169 p hg
    simpa only [d2574, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2574, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22178 p hg
    simpa only [d2574, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22180 (p : Pattern) (guard : d5538 p = 1) : d2575 p ≤ (4 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2575, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22106 p hg
    simpa only [d2575, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2575, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22124 p hg
    simpa only [d2575, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22181 (p : Pattern) (guard : d5538 p = 1) : d2576 p ≤ (4 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2576, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22179 p hg
    simpa only [d2576, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2576, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22180 p hg
    simpa only [d2576, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22182 (p : Pattern) (guard : d0 p = 1) : d2577 p ≤ (4 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22183 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22184 (p : Pattern) (guard : d5502 p = 1) : d2577 p ≤ (4 : Int) + d58 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2556 p hg
    simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22183 p hg
    simpa only [d5502, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22185 (p : Pattern) (guard : d5538 p = 1) : d2577 p ≤ (4 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22182 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22184 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22186 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (4 : Int) + d10 p := by
  omega
theorem compare22187 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (4 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22186 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2557 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22188 (p : Pattern) (guard : d1 p = 1) : d329 p ≤ (4 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22187 p hg
    simpa only [d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2558 p hg
    simpa only [d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22189 (p : Pattern) (guard : d5502 p = 1) : d330 p ≤ (4 : Int) + d58 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22188 p hg
    simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22183 p hg
    simpa only [d5502, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22190 (p : Pattern) (guard : d5538 p = 1) : d2578 p ≤ (4 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22182 p hg
    simpa only [d5538, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22189 p hg
    simpa only [d5538, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22191 (p : Pattern) (guard : d5538 p = 1) : d2579 p ≤ (4 : Int) + d58 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22185 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22190 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22192 (p : Pattern) (guard : d5538 p = 1) : d2580 p ≤ (4 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2580, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22190 p hg
    simpa only [d2580, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2580, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2580, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22193 (p : Pattern) (guard : d5538 p = 1) : d2581 p ≤ (4 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2581, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22191 p hg
    simpa only [d2581, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2581, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22192 p hg
    simpa only [d2581, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22194 (p : Pattern) (guard : d5538 p = 1) : d2582 p ≤ (4 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2582, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22106 p hg
    simpa only [d2582, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2582, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22193 p hg
    simpa only [d2582, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22195 (p : Pattern) (guard : d5502 p = 1) : d2551 p ≤ (4 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2563 p hg
    simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22151 p hg
    simpa only [d5502, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22196 (p : Pattern) (guard : d5538 p = 1) : d2551 p ≤ (4 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22147 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22195 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22197 (p : Pattern) (guard : d5538 p = 1) : d2583 p ≤ (4 : Int) + d40 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22196 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22153 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22198 (p : Pattern) (guard : d5538 p = 1) : d2584 p ≤ (4 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2584, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22197 p hg
    simpa only [d2584, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2584, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22154 p hg
    simpa only [d2584, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22199 (p : Pattern) (guard : d5538 p = 1) : d2585 p ≤ (4 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2585, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d2585, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2585, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2585, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22200 (p : Pattern) (guard : d5538 p = 1) : d2586 p ≤ (4 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2586, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22194 p hg
    simpa only [d2586, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2586, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22199 p hg
    simpa only [d2586, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22201 (p : Pattern) (guard : d5538 p = 1) : d2587 p ≤ (4 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2587, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22181 p hg
    simpa only [d2587, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2587, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22200 p hg
    simpa only [d2587, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22202 (p : Pattern) (guard : d5538 p = 1) : d2588 p ≤ (4 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2588, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22172 p hg
    simpa only [d2588, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2588, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2588, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22203 (p : Pattern) (guard : d5538 p = 1) : d2589 p ≤ (4 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2589, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22145 p hg
    simpa only [d2589, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2589, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22202 p hg
    simpa only [d2589, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22204 (p : Pattern) (guard : d5538 p = 1) : d2590 p ≤ (4 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2590, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22156 p hg
    simpa only [d2590, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2590, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22161 p hg
    simpa only [d2590, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22205 (p : Pattern) (guard : d5538 p = 1) : d2591 p ≤ (4 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2591, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22203 p hg
    simpa only [d2591, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2591, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22204 p hg
    simpa only [d2591, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22206 (p : Pattern) (guard : d5538 p = 1) : d2592 p ≤ (4 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2592, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22191 p hg
    simpa only [d2592, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2592, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2592, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22207 (p : Pattern) (guard : d5538 p = 1) : d2593 p ≤ (4 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2593, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22156 p hg
    simpa only [d2593, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2593, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22206 p hg
    simpa only [d2593, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22208 (p : Pattern) (guard : d5538 p = 1) : d2594 p ≤ (4 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2594, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22197 p hg
    simpa only [d2594, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2594, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2594, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22209 (p : Pattern) (guard : d5538 p = 1) : d2595 p ≤ (4 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2595, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22208 p hg
    simpa only [d2595, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2595, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2595, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22210 (p : Pattern) (guard : d5538 p = 1) : d2596 p ≤ (4 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2596, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22207 p hg
    simpa only [d2596, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2596, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22209 p hg
    simpa only [d2596, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22211 (p : Pattern) (guard : d5538 p = 1) : d2597 p ≤ (4 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2597, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22205 p hg
    simpa only [d2597, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2597, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22210 p hg
    simpa only [d2597, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22212 (p : Pattern) (guard : d5538 p = 1) : d2598 p ≤ (4 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2598, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22201 p hg
    simpa only [d2598, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2598, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22211 p hg
    simpa only [d2598, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22213 (p : Pattern) (guard : d5538 p = 1) : d2599 p ≤ (4 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2599, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22165 p hg
    simpa only [d2599, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2599, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22212 p hg
    simpa only [d2599, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22214 (p : Pattern) (guard : d5538 p = 1) : d2600 p ≤ (4 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2600, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22074 p hg
    simpa only [d2600, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2600, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2600, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22215 (p : Pattern) (guard : d5538 p = 1) : d2601 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2601, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22089 p hg
    simpa only [d2601, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2601, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22214 p hg
    simpa only [d2601, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22216 (p : Pattern) (guard : d5538 p = 1) : d2602 p ≤ (4 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2602, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22099 p hg
    simpa only [d2602, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2602, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2602, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22217 (p : Pattern) (guard : d5538 p = 1) : d2603 p ≤ (4 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2603, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22100 p hg
    simpa only [d2603, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2603, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22216 p hg
    simpa only [d2603, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22218 (p : Pattern) (guard : d5538 p = 1) : d2604 p ≤ (4 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2604, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22215 p hg
    simpa only [d2604, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2604, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22217 p hg
    simpa only [d2604, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22219 (p : Pattern) (guard : d5538 p = 1) : d2605 p ≤ (4 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2605, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22215 p hg
    simpa only [d2605, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2605, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22218 p hg
    simpa only [d2605, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22220 (p : Pattern) (guard : d5538 p = 1) : d2606 p ≤ (4 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2606, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22117 p hg
    simpa only [d2606, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2606, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2606, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22221 (p : Pattern) (guard : d5538 p = 1) : d2607 p ≤ (4 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2607, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22118 p hg
    simpa only [d2607, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2607, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22220 p hg
    simpa only [d2607, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22222 (p : Pattern) (guard : d5538 p = 1) : d2608 p ≤ (4 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2608, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22221 p hg
    simpa only [d2608, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2608, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2608, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22223 (p : Pattern) (guard : d5538 p = 1) : d2609 p ≤ (4 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2609, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22218 p hg
    simpa only [d2609, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2609, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22222 p hg
    simpa only [d2609, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22224 (p : Pattern) (guard : d5538 p = 1) : d2610 p ≤ (4 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2610, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22219 p hg
    simpa only [d2610, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2610, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22223 p hg
    simpa only [d2610, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22225 (p : Pattern) (guard : d5538 p = 1) : d2611 p ≤ (4 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2611, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22172 p hg
    simpa only [d2611, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2611, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22135 p hg
    simpa only [d2611, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22226 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (4 : Int) + d35 p := by
  omega
theorem compare22227 (p : Pattern) (guard : d5502 p = 1) : d2545 p ≤ (4 : Int) + d35 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22226 p hg
    simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22141 p hg
    simpa only [d5502, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22228 (p : Pattern) (guard : d5538 p = 1) : d2545 p ≤ (4 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22137 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22227 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22229 (p : Pattern) (guard : d5538 p = 1) : d2612 p ≤ (4 : Int) + d35 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22228 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22143 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22230 (p : Pattern) (guard : d5538 p = 1) : d2613 p ≤ (4 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2613, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22229 p hg
    simpa only [d2613, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2613, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22144 p hg
    simpa only [d2613, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22231 (p : Pattern) (guard : d5538 p = 1) : d2614 p ≤ (4 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2614, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22225 p hg
    simpa only [d2614, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2614, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22230 p hg
    simpa only [d2614, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22232 (p : Pattern) (guard : d5538 p = 1) : d2615 p ≤ (4 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2615, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22231 p hg
    simpa only [d2615, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2615, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22199 p hg
    simpa only [d2615, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22233 (p : Pattern) (guard : d5538 p = 1) : d2616 p ≤ (4 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2616, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22232 p hg
    simpa only [d2616, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2616, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2616, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22234 (p : Pattern) (guard : d5538 p = 1) : d2617 p ≤ (4 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2617, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22224 p hg
    simpa only [d2617, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2617, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22233 p hg
    simpa only [d2617, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22235 (p : Pattern) (guard : d5538 p = 1) : d2618 p ≤ (4 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2618, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22215 p hg
    simpa only [d2618, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2618, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22225 p hg
    simpa only [d2618, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22236 (p : Pattern) (guard : d5538 p = 1) : d2619 p ≤ (4 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2619, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22217 p hg
    simpa only [d2619, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2619, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22221 p hg
    simpa only [d2619, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22237 (p : Pattern) (guard : d5538 p = 1) : d2620 p ≤ (4 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2620, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22235 p hg
    simpa only [d2620, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2620, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22236 p hg
    simpa only [d2620, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22238 (p : Pattern) (guard : d5538 p = 1) : d2621 p ≤ (4 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2621, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22217 p hg
    simpa only [d2621, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2621, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22193 p hg
    simpa only [d2621, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22239 (p : Pattern) (guard : d5538 p = 1) : d2622 p ≤ (4 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2622, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22238 p hg
    simpa only [d2622, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2622, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22199 p hg
    simpa only [d2622, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22240 (p : Pattern) (guard : d5538 p = 1) : d2623 p ≤ (4 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2623, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22237 p hg
    simpa only [d2623, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2623, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22239 p hg
    simpa only [d2623, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22241 (p : Pattern) (guard : d5538 p = 1) : d2624 p ≤ (4 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2624, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22230 p hg
    simpa only [d2624, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2624, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2624, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22242 (p : Pattern) (guard : d5538 p = 1) : d2625 p ≤ (4 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2625, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22241 p hg
    simpa only [d2625, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2625, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2625, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22243 (p : Pattern) (guard : d5538 p = 1) : d2626 p ≤ (4 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2626, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22242 p hg
    simpa only [d2626, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2626, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2626, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22244 (p : Pattern) (guard : d5538 p = 1) : d2627 p ≤ (4 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2627, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22240 p hg
    simpa only [d2627, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2627, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22243 p hg
    simpa only [d2627, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22245 (p : Pattern) (guard : d5538 p = 1) : d2628 p ≤ (4 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2628, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22234 p hg
    simpa only [d2628, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2628, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22244 p hg
    simpa only [d2628, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22246 (p : Pattern) (guard : d5538 p = 1) : d2629 p ≤ (4 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2629, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22213 p hg
    simpa only [d2629, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2629, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22245 p hg
    simpa only [d2629, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22247 (p : Pattern) (guard : d5538 p = 1) : d2630 p ≤ (4 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2630, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22221 p hg
    simpa only [d2630, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2630, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d2630, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22248 (p : Pattern) (guard : d5538 p = 1) : d2631 p ≤ (4 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2631, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22247 p hg
    simpa only [d2631, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2631, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22199 p hg
    simpa only [d2631, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22249 (p : Pattern) (guard : d5538 p = 1) : d2632 p ≤ (4 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2632, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22199 p hg
    simpa only [d2632, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2632, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2632, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22250 (p : Pattern) (guard : d5538 p = 1) : d2633 p ≤ (4 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2633, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22248 p hg
    simpa only [d2633, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2633, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22249 p hg
    simpa only [d2633, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22251 (p : Pattern) (guard : d5538 p = 1) : d2634 p ≤ (4 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2634, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22249 p hg
    simpa only [d2634, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2634, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2634, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22252 (p : Pattern) (guard : d5538 p = 1) : d2635 p ≤ (4 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2635, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22250 p hg
    simpa only [d2635, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2635, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22251 p hg
    simpa only [d2635, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22253 (p : Pattern) (guard : d5538 p = 1) : d2636 p ≤ (4 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2636, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22251 p hg
    simpa only [d2636, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2636, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2636, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22254 (p : Pattern) (guard : d5538 p = 1) : d2637 p ≤ (4 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2637, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22252 p hg
    simpa only [d2637, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2637, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22253 p hg
    simpa only [d2637, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22255 (p : Pattern) (guard : d5538 p = 1) : d2638 p ≤ (4 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2638, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22245 p hg
    simpa only [d2638, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2638, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22254 p hg
    simpa only [d2638, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22256 (p : Pattern) (guard : d5538 p = 1) : d2639 p ≤ (4 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2639, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22246 p hg
    simpa only [d2639, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2639, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22255 p hg
    simpa only [d2639, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22257 (p : Pattern) (guard : d5538 p = 1) : d2640 p ≤ (4 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22086 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22090 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22258 (p : Pattern) (guard : d5538 p = 1) : d2641 p ≤ (4 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2641, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22257 p hg
    simpa only [d2641, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2641, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22107 p hg
    simpa only [d2641, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22259 (p : Pattern) (guard : d5538 p = 1) : d2642 p ≤ (4 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2642, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22258 p hg
    simpa only [d2642, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2642, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22126 p hg
    simpa only [d2642, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
