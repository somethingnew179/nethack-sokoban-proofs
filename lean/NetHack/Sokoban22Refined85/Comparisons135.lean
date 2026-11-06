/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons134
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18900 (p : Pattern) (guard : d5539 p = 1) : d2432 p ≤ (0 : Int) + d3469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2432, d3469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18690 p hg
    simpa only [d2432, d3469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2432, d3469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18899 p hg
    simpa only [d2432, d3469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18901 (p : Pattern) (guard : d5539 p = 1) : d2433 p ≤ (0 : Int) + d3470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2433, d3470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18900 p hg
    simpa only [d2433, d3470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2433, d3470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18726 p hg
    simpa only [d2433, d3470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18902 (p : Pattern) (guard : d5539 p = 1) : d2434 p ≤ (0 : Int) + d3471 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2434, d3471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18894 p hg
    simpa only [d2434, d3471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2434, d3471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2434, d3471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18903 (p : Pattern) (guard : d5539 p = 1) : d2435 p ≤ (0 : Int) + d3472 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2435, d3472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18902 p hg
    simpa only [d2435, d3472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2435, d3472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2435, d3472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18904 (p : Pattern) (guard : d5539 p = 1) : d2436 p ≤ (0 : Int) + d3473 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2436, d3473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18903 p hg
    simpa only [d2436, d3473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2436, d3473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2436, d3473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18905 (p : Pattern) (guard : d5539 p = 1) : d2437 p ≤ (0 : Int) + d3474 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2437, d3474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18901 p hg
    simpa only [d2437, d3474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2437, d3474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18904 p hg
    simpa only [d2437, d3474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18906 (p : Pattern) (guard : d5539 p = 1) : d2438 p ≤ (0 : Int) + d3475 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2438, d3475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18898 p hg
    simpa only [d2438, d3475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2438, d3475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18905 p hg
    simpa only [d2438, d3475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18907 (p : Pattern) (guard : d5539 p = 1) : d2439 p ≤ (0 : Int) + d3476 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2439, d3476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18888 p hg
    simpa only [d2439, d3476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2439, d3476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18906 p hg
    simpa only [d2439, d3476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18908 (p : Pattern) (guard : d5539 p = 1) : d2440 p ≤ (0 : Int) + d3477 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2440, d3477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18906 p hg
    simpa only [d2440, d3477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2440, d3477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2440, d3477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18909 (p : Pattern) (guard : d5539 p = 1) : d2441 p ≤ (0 : Int) + d3478 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2441, d3478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18907 p hg
    simpa only [d2441, d3478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2441, d3478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18908 p hg
    simpa only [d2441, d3478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18910 (p : Pattern) (guard : d5539 p = 1) : d2442 p ≤ (0 : Int) + d3479 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2442, d3479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18771 p hg
    simpa only [d2442, d3479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2442, d3479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18909 p hg
    simpa only [d2442, d3479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18911 (p : Pattern) (guard : d5539 p = 1) : d2443 p ≤ (0 : Int) + d3480 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2443, d3480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18755 p hg
    simpa only [d2443, d3480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2443, d3480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18910 p hg
    simpa only [d2443, d3480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18912 (p : Pattern) (guard : d5539 p = 1) : d2444 p ≤ (0 : Int) + d3481 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2444, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18794 p hg
    simpa only [d2444, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2444, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2444, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18913 (p : Pattern) (guard : d5539 p = 1) : d2445 p ≤ (0 : Int) + d3482 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2445, d3482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18822 p hg
    simpa only [d2445, d3482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2445, d3482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18912 p hg
    simpa only [d2445, d3482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18914 (p : Pattern) (guard : d5539 p = 1) : d2446 p ≤ (0 : Int) + d3483 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2446, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18912 p hg
    simpa only [d2446, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2446, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2446, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18915 (p : Pattern) (guard : d5539 p = 1) : d2447 p ≤ (0 : Int) + d3484 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2447, d3484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18913 p hg
    simpa only [d2447, d3484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2447, d3484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18914 p hg
    simpa only [d2447, d3484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18916 (p : Pattern) (guard : d5539 p = 1) : d2448 p ≤ (0 : Int) + d3485 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2448, d3485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18810 p hg
    simpa only [d2448, d3485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2448, d3485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2448, d3485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18917 (p : Pattern) (guard : d5539 p = 1) : d2449 p ≤ (0 : Int) + d3486 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2449, d3486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18829 p hg
    simpa only [d2449, d3486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2449, d3486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18916 p hg
    simpa only [d2449, d3486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18918 (p : Pattern) (guard : d5539 p = 1) : d2450 p ≤ (0 : Int) + d3487 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2450, d3487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18916 p hg
    simpa only [d2450, d3487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2450, d3487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2450, d3487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18919 (p : Pattern) (guard : d5539 p = 1) : d2451 p ≤ (0 : Int) + d3488 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2451, d3488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18917 p hg
    simpa only [d2451, d3488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2451, d3488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18918 p hg
    simpa only [d2451, d3488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18920 (p : Pattern) (guard : d5539 p = 1) : d2452 p ≤ (0 : Int) + d3489 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2452, d3489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18915 p hg
    simpa only [d2452, d3489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2452, d3489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18919 p hg
    simpa only [d2452, d3489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18921 (p : Pattern) (guard : d5539 p = 1) : d2453 p ≤ (0 : Int) + d3490 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2453, d3490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18816 p hg
    simpa only [d2453, d3490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2453, d3490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18920 p hg
    simpa only [d2453, d3490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18922 (p : Pattern) (guard : d5539 p = 1) : d2454 p ≤ (0 : Int) + d3491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2454, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18844 p hg
    simpa only [d2454, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2454, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18912 p hg
    simpa only [d2454, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18923 (p : Pattern) (guard : d5539 p = 1) : d2455 p ≤ (0 : Int) + d3492 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2455, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18922 p hg
    simpa only [d2455, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2455, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18914 p hg
    simpa only [d2455, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18924 (p : Pattern) (guard : d5539 p = 1) : d2456 p ≤ (0 : Int) + d3493 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2456, d3493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18923 p hg
    simpa only [d2456, d3493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2456, d3493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18849 p hg
    simpa only [d2456, d3493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18925 (p : Pattern) (guard : d5539 p = 1) : d2457 p ≤ (0 : Int) + d3494 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2457, d3494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18843 p hg
    simpa only [d2457, d3494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2457, d3494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18924 p hg
    simpa only [d2457, d3494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18926 (p : Pattern) (guard : d5539 p = 1) : d2458 p ≤ (0 : Int) + d3495 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2458, d3495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18921 p hg
    simpa only [d2458, d3495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2458, d3495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18925 p hg
    simpa only [d2458, d3495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18927 (p : Pattern) (guard : d5539 p = 1) : d2459 p ≤ (0 : Int) + d3496 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2459, d3496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18925 p hg
    simpa only [d2459, d3496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2459, d3496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18856 p hg
    simpa only [d2459, d3496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18928 (p : Pattern) (guard : d5539 p = 1) : d2460 p ≤ (0 : Int) + d3497 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2460, d3497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18926 p hg
    simpa only [d2460, d3497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2460, d3497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18927 p hg
    simpa only [d2460, d3497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18929 (p : Pattern) (guard : d5539 p = 1) : d2461 p ≤ (0 : Int) + d3498 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2461, d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18801 p hg
    simpa only [d2461, d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2461, d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18806 p hg
    simpa only [d2461, d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18930 (p : Pattern) (guard : d5539 p = 1) : d2462 p ≤ (0 : Int) + d3499 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2462, d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18821 p hg
    simpa only [d2462, d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2462, d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18929 p hg
    simpa only [d2462, d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18931 (p : Pattern) (guard : d5539 p = 1) : d2463 p ≤ (0 : Int) + d3500 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2463, d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18930 p hg
    simpa only [d2463, d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2463, d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18916 p hg
    simpa only [d2463, d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18932 (p : Pattern) (guard : d5539 p = 1) : d2464 p ≤ (0 : Int) + d3501 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2464, d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18805 p hg
    simpa only [d2464, d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2464, d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2464, d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18933 (p : Pattern) (guard : d5539 p = 1) : d2465 p ≤ (0 : Int) + d3502 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2465, d3502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18932 p hg
    simpa only [d2465, d3502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2465, d3502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2465, d3502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18934 (p : Pattern) (guard : d5539 p = 1) : d2466 p ≤ (0 : Int) + d3503 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2466, d3503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18933 p hg
    simpa only [d2466, d3503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2466, d3503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2466, d3503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18935 (p : Pattern) (guard : d5539 p = 1) : d2467 p ≤ (0 : Int) + d3504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2467, d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18931 p hg
    simpa only [d2467, d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2467, d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18934 p hg
    simpa only [d2467, d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18936 (p : Pattern) (guard : d5539 p = 1) : d2468 p ≤ (0 : Int) + d3505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2468, d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18861 p hg
    simpa only [d2468, d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2468, d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18935 p hg
    simpa only [d2468, d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18937 (p : Pattern) (guard : d5539 p = 1) : d2469 p ≤ (0 : Int) + d3506 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2469, d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18792 p hg
    simpa only [d2469, d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2469, d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18806 p hg
    simpa only [d2469, d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18938 (p : Pattern) (guard : d5539 p = 1) : d2470 p ≤ (0 : Int) + d3507 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2470, d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18937 p hg
    simpa only [d2470, d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2470, d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18810 p hg
    simpa only [d2470, d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18939 (p : Pattern) (guard : d5539 p = 1) : d2471 p ≤ (0 : Int) + d3508 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2471, d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18938 p hg
    simpa only [d2471, d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2471, d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18933 p hg
    simpa only [d2471, d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18940 (p : Pattern) (guard : d5539 p = 1) : d2472 p ≤ (0 : Int) + d3509 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2472, d3509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18682 p hg
    simpa only [d2472, d3509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2472, d3509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2472, d3509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18941 (p : Pattern) (guard : d5539 p = 1) : d2473 p ≤ (0 : Int) + d3510 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2473, d3510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18939 p hg
    simpa only [d2473, d3510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2473, d3510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18940 p hg
    simpa only [d2473, d3510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18942 (p : Pattern) (guard : d5539 p = 1) : d2474 p ≤ (0 : Int) + d3511 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2474, d3511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18923 p hg
    simpa only [d2474, d3511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2474, d3511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18941 p hg
    simpa only [d2474, d3511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18943 (p : Pattern) (guard : d5539 p = 1) : d2475 p ≤ (0 : Int) + d3512 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2475, d3512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18936 p hg
    simpa only [d2475, d3512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2475, d3512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18942 p hg
    simpa only [d2475, d3512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18944 (p : Pattern) (guard : d5539 p = 1) : d2476 p ≤ (0 : Int) + d3513 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2476, d3513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18821 p hg
    simpa only [d2476, d3513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2476, d3513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18699 p hg
    simpa only [d2476, d3513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18945 (p : Pattern) (guard : d5539 p = 1) : d2477 p ≤ (0 : Int) + d3514 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2477, d3514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18790 p hg
    simpa only [d2477, d3514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2477, d3514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18944 p hg
    simpa only [d2477, d3514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18946 (p : Pattern) (guard : d5539 p = 1) : d2478 p ≤ (0 : Int) + d3515 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2478, d3515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18945 p hg
    simpa only [d2478, d3515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2478, d3515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18826 p hg
    simpa only [d2478, d3515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18947 (p : Pattern) (guard : d5539 p = 1) : d2479 p ≤ (0 : Int) + d3516 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2479, d3516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18946 p hg
    simpa only [d2479, d3516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2479, d3516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18849 p hg
    simpa only [d2479, d3516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18948 (p : Pattern) (guard : d5539 p = 1) : d2480 p ≤ (0 : Int) + d3517 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2480, d3517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18821 p hg
    simpa only [d2480, d3517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2480, d3517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18912 p hg
    simpa only [d2480, d3517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18949 (p : Pattern) (guard : d5539 p = 1) : d2481 p ≤ (0 : Int) + d3518 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2481, d3518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18948 p hg
    simpa only [d2481, d3518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2481, d3518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18848 p hg
    simpa only [d2481, d3518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18950 (p : Pattern) (guard : d5539 p = 1) : d2482 p ≤ (0 : Int) + d3519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2482, d3519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18660 p hg
    simpa only [d2482, d3519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2482, d3519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2482, d3519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18951 (p : Pattern) (guard : d5539 p = 1) : d2483 p ≤ (0 : Int) + d3520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2483, d3520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18950 p hg
    simpa only [d2483, d3520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2483, d3520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2483, d3520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18952 (p : Pattern) (guard : d5539 p = 1) : d2484 p ≤ (0 : Int) + d3521 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2484, d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18949 p hg
    simpa only [d2484, d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2484, d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18951 p hg
    simpa only [d2484, d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18953 (p : Pattern) (guard : d5539 p = 1) : d2485 p ≤ (0 : Int) + d3522 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2485, d3522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18947 p hg
    simpa only [d2485, d3522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2485, d3522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18952 p hg
    simpa only [d2485, d3522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18954 (p : Pattern) (guard : d5539 p = 1) : d2486 p ≤ (0 : Int) + d3523 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2486, d3523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18943 p hg
    simpa only [d2486, d3523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2486, d3523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18953 p hg
    simpa only [d2486, d3523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18955 (p : Pattern) (guard : d5539 p = 1) : d2487 p ≤ (0 : Int) + d3524 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2487, d3524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18821 p hg
    simpa only [d2487, d3524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2487, d3524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18659 p hg
    simpa only [d2487, d3524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18956 (p : Pattern) (guard : d5539 p = 1) : d2488 p ≤ (0 : Int) + d3525 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2488, d3525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18790 p hg
    simpa only [d2488, d3525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2488, d3525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18955 p hg
    simpa only [d2488, d3525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18957 (p : Pattern) (guard : d5539 p = 1) : d2489 p ≤ (0 : Int) + d3526 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2489, d3526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18794 p hg
    simpa only [d2489, d3526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2489, d3526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18659 p hg
    simpa only [d2489, d3526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18958 (p : Pattern) (guard : d5539 p = 1) : d2490 p ≤ (0 : Int) + d3527 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2490, d3527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18957 p hg
    simpa only [d2490, d3527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2490, d3527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2490, d3527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18959 (p : Pattern) (guard : d5539 p = 1) : d2491 p ≤ (0 : Int) + d3528 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2491, d3528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18956 p hg
    simpa only [d2491, d3528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2491, d3528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18958 p hg
    simpa only [d2491, d3528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18960 (p : Pattern) (guard : d5539 p = 1) : d2492 p ≤ (0 : Int) + d3529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2492, d3529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18839 p hg
    simpa only [d2492, d3529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2492, d3529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18699 p hg
    simpa only [d2492, d3529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18961 (p : Pattern) (guard : d5539 p = 1) : d2493 p ≤ (0 : Int) + d3530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2493, d3530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18960 p hg
    simpa only [d2493, d3530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2493, d3530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2493, d3530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18962 (p : Pattern) (guard : d5539 p = 1) : d2494 p ≤ (0 : Int) + d3531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2494, d3531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18961 p hg
    simpa only [d2494, d3531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2494, d3531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2494, d3531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18963 (p : Pattern) (guard : d5539 p = 1) : d2495 p ≤ (0 : Int) + d3532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2495, d3532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18959 p hg
    simpa only [d2495, d3532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2495, d3532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18962 p hg
    simpa only [d2495, d3532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18964 (p : Pattern) (guard : d5539 p = 1) : d2496 p ≤ (0 : Int) + d3533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2496, d3533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18963 p hg
    simpa only [d2496, d3533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2496, d3533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18952 p hg
    simpa only [d2496, d3533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18965 (p : Pattern) (guard : d5539 p = 1) : d2497 p ≤ (0 : Int) + d3534 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2497, d3534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18964 p hg
    simpa only [d2497, d3534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2497, d3534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d2497, d3534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18966 (p : Pattern) (guard : d5539 p = 1) : d2498 p ≤ (0 : Int) + d3535 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2498, d3535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18954 p hg
    simpa only [d2498, d3535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2498, d3535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18965 p hg
    simpa only [d2498, d3535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18967 (p : Pattern) (guard : d5539 p = 1) : d2499 p ≤ (0 : Int) + d3536 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2499, d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18928 p hg
    simpa only [d2499, d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2499, d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18966 p hg
    simpa only [d2499, d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18968 (p : Pattern) (guard : d5539 p = 1) : d2500 p ≤ (0 : Int) + d3537 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2500, d3537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18755 p hg
    simpa only [d2500, d3537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2500, d3537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18967 p hg
    simpa only [d2500, d3537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18969 (p : Pattern) (guard : d5539 p = 1) : d2501 p ≤ (0 : Int) + d3538 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2501, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18911 p hg
    simpa only [d2501, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2501, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18968 p hg
    simpa only [d2501, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18970 (p : Pattern) (guard : d5539 p = 1) : d2502 p ≤ (0 : Int) + d3539 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d2502, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18870 p hg
    simpa only [d2502, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d2502, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18969 p hg
    simpa only [d2502, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18971 (p : Pattern) (guard : d0 p = 1) : d318 p ≤ (0 : Int) + d2504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18972 (p : Pattern) (guard : d5503 p = 1) : d2184 p ≤ (0 : Int) + d2505 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2184, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14832 p hg
    simpa only [d5503, d2184, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2184, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18971 p hg
    simpa only [d5503, d2184, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18973 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2506 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18974 (p : Pattern) (guard : d5503 p = 1) : d2185 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2185, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d5503, d2185, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2185, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18973 p hg
    simpa only [d5503, d2185, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18975 (p : Pattern) (guard : d5503 p = 1) : d2186 p ≤ (0 : Int) + d2508 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2186, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18972 p hg
    simpa only [d2186, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2186, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18974 p hg
    simpa only [d2186, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18976 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2509 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18977 (p : Pattern) (guard : d5503 p = 1) : d2185 p ≤ (0 : Int) + d2510 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2185, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d5503, d2185, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2185, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18976 p hg
    simpa only [d5503, d2185, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18978 (p : Pattern) (guard : d5503 p = 1) : d2187 p ≤ (0 : Int) + d2511 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2187, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18977 p hg
    simpa only [d2187, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2187, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2187, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18979 (p : Pattern) (guard : d5503 p = 1) : d2188 p ≤ (0 : Int) + d2512 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2188, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18975 p hg
    simpa only [d2188, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2188, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18978 p hg
    simpa only [d2188, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18980 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d2504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18981 (p : Pattern) (guard : d5503 p = 1) : d2189 p ≤ (0 : Int) + d2514 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2189, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14845 p hg
    simpa only [d5503, d2189, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2189, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18980 p hg
    simpa only [d5503, d2189, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18982 (p : Pattern) (guard : d5503 p = 1) : d2190 p ≤ (0 : Int) + d2515 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2190, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18981 p hg
    simpa only [d2190, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2190, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18974 p hg
    simpa only [d2190, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18983 (p : Pattern) (guard : d5503 p = 1) : d2191 p ≤ (0 : Int) + d2516 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2191, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18982 p hg
    simpa only [d2191, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2191, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18978 p hg
    simpa only [d2191, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18984 (p : Pattern) (guard : d5503 p = 1) : d2192 p ≤ (0 : Int) + d2517 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2192, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18979 p hg
    simpa only [d2192, d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2192, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18983 p hg
    simpa only [d2192, d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18985 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d2504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18986 (p : Pattern) (guard : d5503 p = 1) : d2193 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d5503, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18985 p hg
    simpa only [d5503, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18987 (p : Pattern) (guard : d5503 p = 1) : d2194 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2194, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18986 p hg
    simpa only [d2194, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2194, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18974 p hg
    simpa only [d2194, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18988 (p : Pattern) (guard : d5503 p = 1) : d2195 p ≤ (0 : Int) + d2519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2195, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18987 p hg
    simpa only [d2195, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2195, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18978 p hg
    simpa only [d2195, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18989 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2520 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18990 (p : Pattern) (guard : d5503 p = 1) : d2196 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d5503, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18989 p hg
    simpa only [d5503, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18991 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2521 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18992 (p : Pattern) (guard : d5503 p = 1) : d2196 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2196, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d5503, d2196, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2196, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18991 p hg
    simpa only [d5503, d2196, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18993 (p : Pattern) (guard : d5503 p = 1) : d2196 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18990 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18992 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18994 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2524 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18995 (p : Pattern) (guard : d5503 p = 1) : d2196 p ≤ (0 : Int) + d2525 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2196, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d5503, d2196, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2196, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18994 p hg
    simpa only [d5503, d2196, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18996 (p : Pattern) (guard : d5503 p = 1) : d2197 p ≤ (0 : Int) + d2526 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2197, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18995 p hg
    simpa only [d2197, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2197, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2197, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18997 (p : Pattern) (guard : d5503 p = 1) : d2198 p ≤ (0 : Int) + d2527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2198, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18993 p hg
    simpa only [d2198, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2198, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18996 p hg
    simpa only [d2198, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18998 (p : Pattern) (guard : d5503 p = 1) : d2199 p ≤ (0 : Int) + d2528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2199, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18988 p hg
    simpa only [d2199, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2199, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18997 p hg
    simpa only [d2199, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18999 (p : Pattern) (guard : d5503 p = 1) : d2200 p ≤ (0 : Int) + d2529 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2200, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18984 p hg
    simpa only [d2200, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2200, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18998 p hg
    simpa only [d2200, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19000 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19001 (p : Pattern) (guard : d5503 p = 1) : d2185 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d5503, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19000 p hg
    simpa only [d5503, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19002 (p : Pattern) (guard : d5503 p = 1) : d2185 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19001 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18974 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19003 (p : Pattern) (guard : d5503 p = 1) : d2201 p ≤ (0 : Int) + d2519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2201, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19002 p hg
    simpa only [d2201, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2201, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18978 p hg
    simpa only [d2201, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19004 (p : Pattern) (guard : d5503 p = 1) : d2202 p ≤ (0 : Int) + d2528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2202, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19003 p hg
    simpa only [d2202, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2202, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18997 p hg
    simpa only [d2202, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19005 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19006 (p : Pattern) (guard : d5503 p = 1) : d2203 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d5503, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19005 p hg
    simpa only [d5503, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19007 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d357 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19008 (p : Pattern) (guard : d5503 p = 1) : d2203 p ≤ (0 : Int) + d2531 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2203, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d5503, d2203, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2203, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19007 p hg
    simpa only [d5503, d2203, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19009 (p : Pattern) (guard : d5503 p = 1) : d2203 p ≤ (0 : Int) + d2532 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19006 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19008 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19010 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2533 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19011 (p : Pattern) (guard : d5503 p = 1) : d2203 p ≤ (0 : Int) + d2534 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2203, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d5503, d2203, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2203, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19010 p hg
    simpa only [d5503, d2203, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19012 (p : Pattern) (guard : d5503 p = 1) : d2204 p ≤ (0 : Int) + d2535 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2204, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19011 p hg
    simpa only [d2204, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2204, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2204, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19013 (p : Pattern) (guard : d5503 p = 1) : d2205 p ≤ (0 : Int) + d2536 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2205, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19009 p hg
    simpa only [d2205, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2205, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19012 p hg
    simpa only [d2205, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19014 (p : Pattern) (guard : d5503 p = 1) : d2206 p ≤ (0 : Int) + d2537 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2206, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19013 p hg
    simpa only [d2206, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2206, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2206, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19015 (p : Pattern) (guard : d5503 p = 1) : d2207 p ≤ (0 : Int) + d2538 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2207, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19004 p hg
    simpa only [d2207, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2207, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19014 p hg
    simpa only [d2207, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19016 (p : Pattern) (guard : d5503 p = 1) : d2208 p ≤ (0 : Int) + d2539 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2208, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18999 p hg
    simpa only [d2208, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2208, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19015 p hg
    simpa only [d2208, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19017 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2541 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19018 (p : Pattern) (guard : d5503 p = 1) : d2209 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2209, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d5503, d2209, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2209, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19017 p hg
    simpa only [d5503, d2209, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19019 (p : Pattern) (guard : d5503 p = 1) : d2210 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2210, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19018 p hg
    simpa only [d2210, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2210, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2210, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19020 (p : Pattern) (guard : d5503 p = 1) : d2211 p ≤ (0 : Int) + d2544 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2211, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19002 p hg
    simpa only [d2211, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2211, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19019 p hg
    simpa only [d2211, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19021 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2546 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19022 (p : Pattern) (guard : d5503 p = 1) : d2212 p ≤ (0 : Int) + d2547 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2212, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14883 p hg
    simpa only [d5503, d2212, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2212, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19021 p hg
    simpa only [d5503, d2212, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19023 (p : Pattern) (guard : d5503 p = 1) : d2213 p ≤ (0 : Int) + d2548 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2213, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19022 p hg
    simpa only [d2213, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2213, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2213, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19024 (p : Pattern) (guard : d5503 p = 1) : d2214 p ≤ (0 : Int) + d2549 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2214, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19002 p hg
    simpa only [d2214, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2214, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19023 p hg
    simpa only [d2214, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19025 (p : Pattern) (guard : d5503 p = 1) : d2215 p ≤ (0 : Int) + d2550 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2215, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19020 p hg
    simpa only [d2215, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2215, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19024 p hg
    simpa only [d2215, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19026 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19027 (p : Pattern) (guard : d5503 p = 1) : d2216 p ≤ (0 : Int) + d2552 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2216, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14889 p hg
    simpa only [d5503, d2216, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2216, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19026 p hg
    simpa only [d5503, d2216, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19028 (p : Pattern) (guard : d5503 p = 1) : d2217 p ≤ (0 : Int) + d2553 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2217, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19027 p hg
    simpa only [d2217, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2217, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2217, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19029 (p : Pattern) (guard : d5503 p = 1) : d2218 p ≤ (0 : Int) + d2554 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2218, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19002 p hg
    simpa only [d2218, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2218, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19028 p hg
    simpa only [d2218, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19030 (p : Pattern) (guard : d5503 p = 1) : d2219 p ≤ (0 : Int) + d2555 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2219, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18993 p hg
    simpa only [d2219, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2219, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2219, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19031 (p : Pattern) (guard : d5503 p = 1) : d2220 p ≤ (0 : Int) + d2556 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2220, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19029 p hg
    simpa only [d2220, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2220, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19030 p hg
    simpa only [d2220, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19032 (p : Pattern) (guard : d5503 p = 1) : d2221 p ≤ (0 : Int) + d2557 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2221, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19025 p hg
    simpa only [d2221, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2221, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19031 p hg
    simpa only [d2221, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19033 (p : Pattern) (guard : d5503 p = 1) : d2222 p ≤ (0 : Int) + d2558 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2222, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19002 p hg
    simpa only [d2222, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2222, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2222, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19034 (p : Pattern) (guard : d5503 p = 1) : d2223 p ≤ (0 : Int) + d2559 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2223, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19033 p hg
    simpa only [d2223, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2223, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19030 p hg
    simpa only [d2223, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19035 (p : Pattern) (guard : d5503 p = 1) : d2224 p ≤ (0 : Int) + d2560 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2224, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19009 p hg
    simpa only [d2224, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2224, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2224, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19036 (p : Pattern) (guard : d5503 p = 1) : d2225 p ≤ (0 : Int) + d2561 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2225, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19035 p hg
    simpa only [d2225, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2225, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2225, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19037 (p : Pattern) (guard : d5503 p = 1) : d2226 p ≤ (0 : Int) + d2562 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2226, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19034 p hg
    simpa only [d2226, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2226, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19036 p hg
    simpa only [d2226, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19038 (p : Pattern) (guard : d5503 p = 1) : d2227 p ≤ (0 : Int) + d2563 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2227, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19032 p hg
    simpa only [d2227, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2227, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19037 p hg
    simpa only [d2227, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19039 (p : Pattern) (guard : d5503 p = 1) : d2228 p ≤ (0 : Int) + d2564 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2228, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19016 p hg
    simpa only [d2228, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2228, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19038 p hg
    simpa only [d2228, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
