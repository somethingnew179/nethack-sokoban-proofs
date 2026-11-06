/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons167
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23520 (p : Pattern) (guard : d5855 p = 1) : d2597 p ≤ (0 : Int) + d3296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2597, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23514 p hg
    simpa only [d2597, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2597, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23519 p hg
    simpa only [d2597, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23521 (p : Pattern) (guard : d5855 p = 1) : d2598 p ≤ (0 : Int) + d3297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2598, d3297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23510 p hg
    simpa only [d2598, d3297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2598, d3297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23520 p hg
    simpa only [d2598, d3297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23522 (p : Pattern) (guard : d5855 p = 1) : d2599 p ≤ (0 : Int) + d3298 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2599, d3298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23467 p hg
    simpa only [d2599, d3298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2599, d3298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23521 p hg
    simpa only [d2599, d3298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23523 (p : Pattern) (guard : d5855 p = 1) : d2600 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2600, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23373 p hg
    simpa only [d2600, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2600, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2600, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23524 (p : Pattern) (guard : d5855 p = 1) : d2601 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2601, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23390 p hg
    simpa only [d2601, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2601, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23523 p hg
    simpa only [d2601, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23525 (p : Pattern) (guard : d5855 p = 1) : d2602 p ≤ (0 : Int) + d3240 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2602, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23401 p hg
    simpa only [d2602, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2602, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2602, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23526 (p : Pattern) (guard : d5855 p = 1) : d2603 p ≤ (0 : Int) + d3241 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2603, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23402 p hg
    simpa only [d2603, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2603, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23525 p hg
    simpa only [d2603, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23527 (p : Pattern) (guard : d5855 p = 1) : d2604 p ≤ (0 : Int) + d3242 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2604, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23524 p hg
    simpa only [d2604, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2604, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23526 p hg
    simpa only [d2604, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23528 (p : Pattern) (guard : d5855 p = 1) : d2605 p ≤ (0 : Int) + d3299 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2605, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23524 p hg
    simpa only [d2605, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2605, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23527 p hg
    simpa only [d2605, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23529 (p : Pattern) (guard : d5855 p = 1) : d2606 p ≤ (0 : Int) + d3245 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2606, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23421 p hg
    simpa only [d2606, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2606, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2606, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23530 (p : Pattern) (guard : d5855 p = 1) : d2607 p ≤ (0 : Int) + d3246 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2607, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23422 p hg
    simpa only [d2607, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2607, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23529 p hg
    simpa only [d2607, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23531 (p : Pattern) (guard : d5855 p = 1) : d2608 p ≤ (0 : Int) + d3247 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2608, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23530 p hg
    simpa only [d2608, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2608, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2608, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23532 (p : Pattern) (guard : d5855 p = 1) : d2609 p ≤ (0 : Int) + d3248 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2609, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23527 p hg
    simpa only [d2609, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2609, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23531 p hg
    simpa only [d2609, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23533 (p : Pattern) (guard : d5855 p = 1) : d2610 p ≤ (0 : Int) + d3300 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2610, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23528 p hg
    simpa only [d2610, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2610, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23532 p hg
    simpa only [d2610, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23534 (p : Pattern) (guard : d5855 p = 1) : d2611 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2611, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23477 p hg
    simpa only [d2611, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2611, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23439 p hg
    simpa only [d2611, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23535 (p : Pattern) (guard : d5843 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare23536 (p : Pattern) (guard : d5847 p = 1) : d35 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23535 p hg
    simpa only [d5847, d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23537 (p : Pattern) (guard : d5854 p = 1) : d2545 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23536 p hg
    simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18667 p hg
    simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23538 (p : Pattern) (guard : d5855 p = 1) : d2545 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23441 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23537 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23539 (p : Pattern) (guard : d5855 p = 1) : d2612 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23538 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23446 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23540 (p : Pattern) (guard : d5855 p = 1) : d2613 p ≤ (0 : Int) + d3301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2613, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23539 p hg
    simpa only [d2613, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2613, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23447 p hg
    simpa only [d2613, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23541 (p : Pattern) (guard : d5855 p = 1) : d2614 p ≤ (0 : Int) + d3302 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2614, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23534 p hg
    simpa only [d2614, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2614, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23540 p hg
    simpa only [d2614, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23542 (p : Pattern) (guard : d5855 p = 1) : d2615 p ≤ (0 : Int) + d3303 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2615, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23541 p hg
    simpa only [d2615, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2615, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23508 p hg
    simpa only [d2615, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23543 (p : Pattern) (guard : d5855 p = 1) : d2616 p ≤ (0 : Int) + d3304 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2616, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23542 p hg
    simpa only [d2616, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2616, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2616, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23544 (p : Pattern) (guard : d5855 p = 1) : d2617 p ≤ (0 : Int) + d3305 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2617, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23533 p hg
    simpa only [d2617, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2617, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23543 p hg
    simpa only [d2617, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23545 (p : Pattern) (guard : d5855 p = 1) : d2618 p ≤ (0 : Int) + d3306 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2618, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23524 p hg
    simpa only [d2618, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2618, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23534 p hg
    simpa only [d2618, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23546 (p : Pattern) (guard : d5855 p = 1) : d2619 p ≤ (0 : Int) + d3277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2619, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23526 p hg
    simpa only [d2619, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2619, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23530 p hg
    simpa only [d2619, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23547 (p : Pattern) (guard : d5855 p = 1) : d2620 p ≤ (0 : Int) + d3307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2620, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23545 p hg
    simpa only [d2620, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2620, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23546 p hg
    simpa only [d2620, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23548 (p : Pattern) (guard : d5855 p = 1) : d2621 p ≤ (0 : Int) + d3282 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2621, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23526 p hg
    simpa only [d2621, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2621, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23500 p hg
    simpa only [d2621, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23549 (p : Pattern) (guard : d5855 p = 1) : d2622 p ≤ (0 : Int) + d3285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2622, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23548 p hg
    simpa only [d2622, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2622, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23508 p hg
    simpa only [d2622, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23550 (p : Pattern) (guard : d5855 p = 1) : d2623 p ≤ (0 : Int) + d3308 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2623, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23547 p hg
    simpa only [d2623, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2623, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23549 p hg
    simpa only [d2623, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23551 (p : Pattern) (guard : d5855 p = 1) : d2624 p ≤ (0 : Int) + d3309 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2624, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23540 p hg
    simpa only [d2624, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2624, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2624, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23552 (p : Pattern) (guard : d5855 p = 1) : d2625 p ≤ (0 : Int) + d3310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2625, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23551 p hg
    simpa only [d2625, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2625, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2625, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23553 (p : Pattern) (guard : d5855 p = 1) : d2626 p ≤ (0 : Int) + d3311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2626, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23552 p hg
    simpa only [d2626, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2626, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2626, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23554 (p : Pattern) (guard : d5855 p = 1) : d2627 p ≤ (0 : Int) + d3312 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2627, d3312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23550 p hg
    simpa only [d2627, d3312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2627, d3312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23553 p hg
    simpa only [d2627, d3312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23555 (p : Pattern) (guard : d5855 p = 1) : d2628 p ≤ (0 : Int) + d3313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2628, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23544 p hg
    simpa only [d2628, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2628, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23554 p hg
    simpa only [d2628, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23556 (p : Pattern) (guard : d5855 p = 1) : d2629 p ≤ (0 : Int) + d3314 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2629, d3314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23522 p hg
    simpa only [d2629, d3314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2629, d3314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23555 p hg
    simpa only [d2629, d3314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23557 (p : Pattern) (guard : d5855 p = 1) : d2630 p ≤ (0 : Int) + d3315 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2630, d3315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23530 p hg
    simpa only [d2630, d3315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2630, d3315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23507 p hg
    simpa only [d2630, d3315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23558 (p : Pattern) (guard : d5855 p = 1) : d2631 p ≤ (0 : Int) + d3316 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2631, d3316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23557 p hg
    simpa only [d2631, d3316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2631, d3316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23508 p hg
    simpa only [d2631, d3316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23559 (p : Pattern) (guard : d5855 p = 1) : d2632 p ≤ (0 : Int) + d3317 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2632, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23508 p hg
    simpa only [d2632, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2632, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2632, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23560 (p : Pattern) (guard : d5855 p = 1) : d2633 p ≤ (0 : Int) + d3318 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2633, d3318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23558 p hg
    simpa only [d2633, d3318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2633, d3318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23559 p hg
    simpa only [d2633, d3318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23561 (p : Pattern) (guard : d5855 p = 1) : d2634 p ≤ (0 : Int) + d3319 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2634, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23559 p hg
    simpa only [d2634, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2634, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2634, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23562 (p : Pattern) (guard : d5855 p = 1) : d2635 p ≤ (0 : Int) + d3320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2635, d3320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23560 p hg
    simpa only [d2635, d3320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2635, d3320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23561 p hg
    simpa only [d2635, d3320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23563 (p : Pattern) (guard : d5855 p = 1) : d2636 p ≤ (0 : Int) + d3321 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2636, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23561 p hg
    simpa only [d2636, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2636, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2636, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23564 (p : Pattern) (guard : d5855 p = 1) : d2637 p ≤ (0 : Int) + d3322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2637, d3322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23562 p hg
    simpa only [d2637, d3322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2637, d3322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23563 p hg
    simpa only [d2637, d3322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23565 (p : Pattern) (guard : d5855 p = 1) : d2638 p ≤ (0 : Int) + d3323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2638, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23555 p hg
    simpa only [d2638, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2638, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23564 p hg
    simpa only [d2638, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23566 (p : Pattern) (guard : d5855 p = 1) : d2639 p ≤ (0 : Int) + d3324 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2639, d3324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23556 p hg
    simpa only [d2639, d3324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2639, d3324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23565 p hg
    simpa only [d2639, d3324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23567 (p : Pattern) (guard : d5855 p = 1) : d2640 p ≤ (0 : Int) + d3325 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2640, d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d2640, d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2640, d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23391 p hg
    simpa only [d2640, d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23568 (p : Pattern) (guard : d5855 p = 1) : d2641 p ≤ (0 : Int) + d3326 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2641, d3326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23567 p hg
    simpa only [d2641, d3326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2641, d3326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23410 p hg
    simpa only [d2641, d3326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23569 (p : Pattern) (guard : d5855 p = 1) : d2642 p ≤ (0 : Int) + d3327 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2642, d3327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23568 p hg
    simpa only [d2642, d3327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2642, d3327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23431 p hg
    simpa only [d2642, d3327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23570 (p : Pattern) (guard : d5855 p = 1) : d2643 p ≤ (0 : Int) + d3328 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2643, d3328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23569 p hg
    simpa only [d2643, d3328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2643, d3328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23466 p hg
    simpa only [d2643, d3328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23571 (p : Pattern) (guard : d5855 p = 1) : d2644 p ≤ (0 : Int) + d3306 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2644, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23391 p hg
    simpa only [d2644, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2644, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23484 p hg
    simpa only [d2644, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23572 (p : Pattern) (guard : d5855 p = 1) : d2645 p ≤ (0 : Int) + d3307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2645, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23571 p hg
    simpa only [d2645, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2645, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23486 p hg
    simpa only [d2645, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23573 (p : Pattern) (guard : d5855 p = 1) : d2646 p ≤ (0 : Int) + d3308 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2646, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23572 p hg
    simpa only [d2646, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2646, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23509 p hg
    simpa only [d2646, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23574 (p : Pattern) (guard : d5855 p = 1) : d2647 p ≤ (0 : Int) + d3329 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2647, d3329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23573 p hg
    simpa only [d2647, d3329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2647, d3329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23520 p hg
    simpa only [d2647, d3329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23575 (p : Pattern) (guard : d5855 p = 1) : d2648 p ≤ (0 : Int) + d3330 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2648, d3330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23570 p hg
    simpa only [d2648, d3330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2648, d3330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23574 p hg
    simpa only [d2648, d3330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23576 (p : Pattern) (guard : d5855 p = 1) : d2649 p ≤ (0 : Int) + d3331 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2649, d3331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23575 p hg
    simpa only [d2649, d3331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2649, d3331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23555 p hg
    simpa only [d2649, d3331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23577 (p : Pattern) (guard : d5855 p = 1) : d2650 p ≤ (0 : Int) + d3332 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2650, d3332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23555 p hg
    simpa only [d2650, d3332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2650, d3332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2650, d3332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23578 (p : Pattern) (guard : d5855 p = 1) : d2651 p ≤ (0 : Int) + d3333 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2651, d3333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23576 p hg
    simpa only [d2651, d3333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2651, d3333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23577 p hg
    simpa only [d2651, d3333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23579 (p : Pattern) (guard : d5855 p = 1) : d2652 p ≤ (0 : Int) + d3334 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2652, d3334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23566 p hg
    simpa only [d2652, d3334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2652, d3334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23578 p hg
    simpa only [d2652, d3334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23580 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23581 (p : Pattern) (guard : d5851 p = 1) : d2653 p ≤ (0 : Int) + d3336 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2653, d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17764 p hg
    simpa only [d5851, d2653, d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2653, d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23580 p hg
    simpa only [d5851, d2653, d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23582 (p : Pattern) (guard : d5855 p = 1) : d2654 p ≤ (0 : Int) + d3337 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2654, d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23581 p hg
    simpa only [d5855, d2654, d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2654, d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23366 p hg
    simpa only [d5855, d2654, d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23583 (p : Pattern) (guard : d5855 p = 1) : d2655 p ≤ (0 : Int) + d3338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2655, d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23582 p hg
    simpa only [d2655, d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2655, d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23373 p hg
    simpa only [d2655, d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23584 (p : Pattern) (guard : d5855 p = 1) : d2656 p ≤ (0 : Int) + d3339 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2656, d3339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23583 p hg
    simpa only [d2656, d3339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2656, d3339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d2656, d3339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23585 (p : Pattern) (guard : d5855 p = 1) : d2657 p ≤ (0 : Int) + d3340 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2657, d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23584 p hg
    simpa only [d2657, d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2657, d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23391 p hg
    simpa only [d2657, d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23586 (p : Pattern) (guard : d5855 p = 1) : d2658 p ≤ (0 : Int) + d3341 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2658, d3341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23585 p hg
    simpa only [d2658, d3341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2658, d3341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23410 p hg
    simpa only [d2658, d3341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23587 (p : Pattern) (guard : d5855 p = 1) : d2659 p ≤ (0 : Int) + d3342 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2659, d3342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23586 p hg
    simpa only [d2659, d3342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2659, d3342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23431 p hg
    simpa only [d2659, d3342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23588 (p : Pattern) (guard : d5855 p = 1) : d2660 p ≤ (0 : Int) + d3343 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2660, d3343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23587 p hg
    simpa only [d2660, d3343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2660, d3343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23466 p hg
    simpa only [d2660, d3343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23589 (p : Pattern) (guard : d5855 p = 1) : d2661 p ≤ (0 : Int) + d3344 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2661, d3344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d2661, d3344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2661, d3344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23484 p hg
    simpa only [d2661, d3344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23590 (p : Pattern) (guard : d5855 p = 1) : d2662 p ≤ (0 : Int) + d3345 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2662, d3345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23589 p hg
    simpa only [d2662, d3345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2662, d3345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23486 p hg
    simpa only [d2662, d3345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23591 (p : Pattern) (guard : d5855 p = 1) : d2663 p ≤ (0 : Int) + d3346 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2663, d3346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23590 p hg
    simpa only [d2663, d3346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2663, d3346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23509 p hg
    simpa only [d2663, d3346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23592 (p : Pattern) (guard : d5855 p = 1) : d2664 p ≤ (0 : Int) + d3347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2664, d3347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23591 p hg
    simpa only [d2664, d3347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2664, d3347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23520 p hg
    simpa only [d2664, d3347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23593 (p : Pattern) (guard : d5855 p = 1) : d2665 p ≤ (0 : Int) + d3348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2665, d3348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23588 p hg
    simpa only [d2665, d3348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2665, d3348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23592 p hg
    simpa only [d2665, d3348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23594 (p : Pattern) (guard : d5855 p = 1) : d2666 p ≤ (0 : Int) + d3349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2666, d3349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23593 p hg
    simpa only [d2666, d3349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2666, d3349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23555 p hg
    simpa only [d2666, d3349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23595 (p : Pattern) (guard : d5855 p = 1) : d2667 p ≤ (0 : Int) + d3350 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2667, d3350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23594 p hg
    simpa only [d2667, d3350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2667, d3350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23565 p hg
    simpa only [d2667, d3350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23596 (p : Pattern) (guard : d5855 p = 1) : d2668 p ≤ (0 : Int) + d3299 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2668, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23391 p hg
    simpa only [d2668, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2668, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23410 p hg
    simpa only [d2668, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23597 (p : Pattern) (guard : d5855 p = 1) : d2669 p ≤ (0 : Int) + d3300 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2669, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23596 p hg
    simpa only [d2669, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2669, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23431 p hg
    simpa only [d2669, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23598 (p : Pattern) (guard : d5855 p = 1) : d2670 p ≤ (0 : Int) + d3351 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2670, d3351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23597 p hg
    simpa only [d2670, d3351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2670, d3351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23466 p hg
    simpa only [d2670, d3351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23599 (p : Pattern) (guard : d5855 p = 1) : d2671 p ≤ (0 : Int) + d3352 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2671, d3352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23598 p hg
    simpa only [d2671, d3352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2671, d3352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23574 p hg
    simpa only [d2671, d3352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23600 (p : Pattern) (guard : d5855 p = 1) : d2672 p ≤ (0 : Int) + d3353 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2672, d3353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23599 p hg
    simpa only [d2672, d3353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2672, d3353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23555 p hg
    simpa only [d2672, d3353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23601 (p : Pattern) (guard : d5855 p = 1) : d2673 p ≤ (0 : Int) + d3354 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2673, d3354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23600 p hg
    simpa only [d2673, d3354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2673, d3354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23577 p hg
    simpa only [d2673, d3354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23602 (p : Pattern) (guard : d5855 p = 1) : d2674 p ≤ (0 : Int) + d3355 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2674, d3355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23595 p hg
    simpa only [d2674, d3355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2674, d3355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23601 p hg
    simpa only [d2674, d3355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23603 (p : Pattern) (guard : d5855 p = 1) : d2675 p ≤ (0 : Int) + d3356 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2675, d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23579 p hg
    simpa only [d2675, d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2675, d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23602 p hg
    simpa only [d2675, d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23604 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d3358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23605 (p : Pattern) (guard : d5851 p = 1) : d2676 p ≤ (0 : Int) + d3359 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2676, d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17787 p hg
    simpa only [d5851, d2676, d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2676, d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23604 p hg
    simpa only [d5851, d2676, d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23606 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d1 p := by
  omega
theorem compare23607 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23606 p hg
    simpa only [d5847, d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23608 (p : Pattern) (guard : d5854 p = 1) : d2677 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23607 p hg
    simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18780 p hg
    simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23609 (p : Pattern) (guard : d5855 p = 1) : d2678 p ≤ (0 : Int) + d3360 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2678, d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23605 p hg
    simpa only [d5855, d2678, d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2678, d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23608 p hg
    simpa only [d5855, d2678, d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23610 (p : Pattern) (guard : d5851 p = 1) : d2677 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d5851, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18780 p hg
    simpa only [d5851, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23611 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23612 (p : Pattern) (guard : d5843 p = 1) : d1939 p ≤ (0 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23611 p hg
    simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23613 (p : Pattern) (guard : d5847 p = 1) : d1940 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1940, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23612 p hg
    simpa only [d5847, d1940, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1940, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d1940, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23614 (p : Pattern) (guard : d5854 p = 1) : d2679 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23613 p hg
    simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18780 p hg
    simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23615 (p : Pattern) (guard : d5855 p = 1) : d2680 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23610 p hg
    simpa only [d5855, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23614 p hg
    simpa only [d5855, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23616 (p : Pattern) (guard : d5855 p = 1) : d2681 p ≤ (0 : Int) + d3361 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2681, d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23609 p hg
    simpa only [d2681, d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2681, d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23615 p hg
    simpa only [d2681, d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23617 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23618 (p : Pattern) (guard : d5843 p = 1) : d1872 p ≤ (0 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23617 p hg
    simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23619 (p : Pattern) (guard : d5847 p = 1) : d1873 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1873, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23618 p hg
    simpa only [d5847, d1873, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1873, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d1873, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23620 (p : Pattern) (guard : d5854 p = 1) : d2682 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23619 p hg
    simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18780 p hg
    simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23621 (p : Pattern) (guard : d5855 p = 1) : d2683 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23610 p hg
    simpa only [d5855, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23620 p hg
    simpa only [d5855, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23622 (p : Pattern) (guard : d5855 p = 1) : d2684 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2684, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23621 p hg
    simpa only [d2684, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2684, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2684, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23623 (p : Pattern) (guard : d5855 p = 1) : d2685 p ≤ (0 : Int) + d3363 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2685, d3363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23616 p hg
    simpa only [d2685, d3363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2685, d3363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23622 p hg
    simpa only [d2685, d3363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23624 (p : Pattern) (guard : d5855 p = 1) : d2677 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23610 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23608 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23625 (p : Pattern) (guard : d5855 p = 1) : d2686 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23624 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23615 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23626 (p : Pattern) (guard : d5855 p = 1) : d2687 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2687, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23625 p hg
    simpa only [d2687, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2687, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23622 p hg
    simpa only [d2687, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23627 (p : Pattern) (guard : d5855 p = 1) : d2688 p ≤ (0 : Int) + d3365 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2688, d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23623 p hg
    simpa only [d2688, d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2688, d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23626 p hg
    simpa only [d2688, d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23628 (p : Pattern) (guard : d5851 p = 1) : d2689 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17798 p hg
    simpa only [d5851, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18791 p hg
    simpa only [d5851, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23629 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare23630 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23629 p hg
    simpa only [d5847, d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23631 (p : Pattern) (guard : d5854 p = 1) : d2689 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23630 p hg
    simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18791 p hg
    simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23632 (p : Pattern) (guard : d5855 p = 1) : d2689 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23628 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23631 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23633 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23634 (p : Pattern) (guard : d5843 p = 1) : d1963 p ≤ (0 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23633 p hg
    simpa only [d5843, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23635 (p : Pattern) (guard : d5847 p = 1) : d1964 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1964, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23634 p hg
    simpa only [d5847, d1964, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1964, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d1964, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23636 (p : Pattern) (guard : d5854 p = 1) : d2690 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23635 p hg
    simpa only [d5854, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18791 p hg
    simpa only [d5854, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23637 (p : Pattern) (guard : d5855 p = 1) : d2691 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23628 p hg
    simpa only [d5855, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23636 p hg
    simpa only [d5855, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23638 (p : Pattern) (guard : d5855 p = 1) : d2692 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23632 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23637 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23639 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23640 (p : Pattern) (guard : d5843 p = 1) : d1880 p ≤ (0 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23639 p hg
    simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23641 (p : Pattern) (guard : d5847 p = 1) : d1881 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1881, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23640 p hg
    simpa only [d5847, d1881, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1881, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d1881, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23642 (p : Pattern) (guard : d5854 p = 1) : d2693 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23641 p hg
    simpa only [d5854, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18791 p hg
    simpa only [d5854, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23643 (p : Pattern) (guard : d5855 p = 1) : d2694 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23628 p hg
    simpa only [d5855, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23642 p hg
    simpa only [d5855, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23644 (p : Pattern) (guard : d5855 p = 1) : d2695 p ≤ (0 : Int) + d3367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2695, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23643 p hg
    simpa only [d2695, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2695, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2695, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23645 (p : Pattern) (guard : d5855 p = 1) : d2696 p ≤ (0 : Int) + d3368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2696, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23638 p hg
    simpa only [d2696, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2696, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23644 p hg
    simpa only [d2696, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23646 (p : Pattern) (guard : d5855 p = 1) : d2697 p ≤ (0 : Int) + d3369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2697, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23626 p hg
    simpa only [d2697, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2697, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23645 p hg
    simpa only [d2697, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23647 (p : Pattern) (guard : d5855 p = 1) : d2698 p ≤ (0 : Int) + d3370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2698, d3370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23627 p hg
    simpa only [d2698, d3370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2698, d3370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23646 p hg
    simpa only [d2698, d3370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23648 (p : Pattern) (guard : d5855 p = 1) : d2699 p ≤ (0 : Int) + d3371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2699, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23500 p hg
    simpa only [d2699, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2699, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2699, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23649 (p : Pattern) (guard : d5855 p = 1) : d2700 p ≤ (0 : Int) + d3372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2700, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23646 p hg
    simpa only [d2700, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2700, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23648 p hg
    simpa only [d2700, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23650 (p : Pattern) (guard : d5855 p = 1) : d2701 p ≤ (0 : Int) + d3373 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2701, d3373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23647 p hg
    simpa only [d2701, d3373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2701, d3373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23649 p hg
    simpa only [d2701, d3373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23651 (p : Pattern) (guard : d5851 p = 1) : d2702 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17807 p hg
    simpa only [d5851, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18800 p hg
    simpa only [d5851, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23652 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23653 (p : Pattern) (guard : d5843 p = 1) : d1894 p ≤ (0 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23652 p hg
    simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23654 (p : Pattern) (guard : d5847 p = 1) : d1895 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1895, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23653 p hg
    simpa only [d5847, d1895, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1895, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d1895, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23655 (p : Pattern) (guard : d5854 p = 1) : d2703 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23654 p hg
    simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18800 p hg
    simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23656 (p : Pattern) (guard : d5855 p = 1) : d2704 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23651 p hg
    simpa only [d5855, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23655 p hg
    simpa only [d5855, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23657 (p : Pattern) (guard : d5855 p = 1) : d2705 p ≤ (0 : Int) + d3375 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2705, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23656 p hg
    simpa only [d2705, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2705, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2705, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23658 (p : Pattern) (guard : d5855 p = 1) : d2706 p ≤ (0 : Int) + d3376 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2706, d3376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23625 p hg
    simpa only [d2706, d3376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2706, d3376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23657 p hg
    simpa only [d2706, d3376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23659 (p : Pattern) (guard : d5851 p = 1) : d2707 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17811 p hg
    simpa only [d5851, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18804 p hg
    simpa only [d5851, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
