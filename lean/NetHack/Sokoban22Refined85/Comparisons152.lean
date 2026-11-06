/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons151
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21280 (p : Pattern) (guard : d5502 p = 1) : d2647 p ≤ (0 : Int) + d2946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2647, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21279 p hg
    simpa only [d2647, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2647, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21214 p hg
    simpa only [d2647, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21281 (p : Pattern) (guard : d5502 p = 1) : d2648 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2648, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21276 p hg
    simpa only [d2648, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2648, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21280 p hg
    simpa only [d2648, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21282 (p : Pattern) (guard : d5502 p = 1) : d2649 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2649, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21281 p hg
    simpa only [d2649, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2649, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21261 p hg
    simpa only [d2649, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21283 (p : Pattern) (guard : d5502 p = 1) : d2650 p ≤ (0 : Int) + d2990 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2650, d2990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21261 p hg
    simpa only [d2650, d2990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2650, d2990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2650, d2990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21284 (p : Pattern) (guard : d5502 p = 1) : d2651 p ≤ (0 : Int) + d2991 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2651, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21282 p hg
    simpa only [d2651, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2651, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21283 p hg
    simpa only [d2651, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21285 (p : Pattern) (guard : d5502 p = 1) : d2652 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2652, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21272 p hg
    simpa only [d2652, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2652, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21284 p hg
    simpa only [d2652, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21286 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21287 (p : Pattern) (guard : d5502 p = 1) : d2653 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21286 p hg
    simpa only [d5502, d2653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21288 (p : Pattern) (guard : d5502 p = 1) : d2654 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21287 p hg
    simpa only [d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21289 (p : Pattern) (guard : d5502 p = 1) : d2655 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2655, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21288 p hg
    simpa only [d2655, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2655, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21093 p hg
    simpa only [d2655, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21290 (p : Pattern) (guard : d5502 p = 1) : d2656 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2656, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21289 p hg
    simpa only [d2656, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2656, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21099 p hg
    simpa only [d2656, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21291 (p : Pattern) (guard : d5502 p = 1) : d2657 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21290 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21108 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21292 (p : Pattern) (guard : d5502 p = 1) : d2658 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2658, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21291 p hg
    simpa only [d2658, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2658, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21119 p hg
    simpa only [d2658, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21293 (p : Pattern) (guard : d5502 p = 1) : d2659 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2659, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21292 p hg
    simpa only [d2659, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2659, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21132 p hg
    simpa only [d2659, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21294 (p : Pattern) (guard : d5502 p = 1) : d2660 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2660, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21293 p hg
    simpa only [d2660, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2660, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21170 p hg
    simpa only [d2660, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21295 (p : Pattern) (guard : d5502 p = 1) : d2661 p ≤ (0 : Int) + d2924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2661, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21105 p hg
    simpa only [d2661, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2661, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21186 p hg
    simpa only [d2661, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21296 (p : Pattern) (guard : d5502 p = 1) : d2662 p ≤ (0 : Int) + d2926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2662, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21295 p hg
    simpa only [d2662, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2662, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21188 p hg
    simpa only [d2662, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21297 (p : Pattern) (guard : d5502 p = 1) : d2663 p ≤ (0 : Int) + d2934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2663, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21296 p hg
    simpa only [d2663, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2663, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21202 p hg
    simpa only [d2663, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21298 (p : Pattern) (guard : d5502 p = 1) : d2664 p ≤ (0 : Int) + d2946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2664, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21297 p hg
    simpa only [d2664, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2664, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21214 p hg
    simpa only [d2664, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21299 (p : Pattern) (guard : d5502 p = 1) : d2665 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2665, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21294 p hg
    simpa only [d2665, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2665, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21298 p hg
    simpa only [d2665, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21300 (p : Pattern) (guard : d5502 p = 1) : d2666 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2666, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21299 p hg
    simpa only [d2666, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2666, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21261 p hg
    simpa only [d2666, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21301 (p : Pattern) (guard : d5502 p = 1) : d2667 p ≤ (0 : Int) + d2989 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2667, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21300 p hg
    simpa only [d2667, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2667, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21271 p hg
    simpa only [d2667, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21302 (p : Pattern) (guard : d5502 p = 1) : d2668 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2668, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21108 p hg
    simpa only [d2668, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2668, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21119 p hg
    simpa only [d2668, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21303 (p : Pattern) (guard : d5502 p = 1) : d2669 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2669, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21302 p hg
    simpa only [d2669, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2669, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21132 p hg
    simpa only [d2669, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21304 (p : Pattern) (guard : d5502 p = 1) : d2670 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2670, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21303 p hg
    simpa only [d2670, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2670, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21170 p hg
    simpa only [d2670, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21305 (p : Pattern) (guard : d5502 p = 1) : d2671 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2671, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21304 p hg
    simpa only [d2671, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2671, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21280 p hg
    simpa only [d2671, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21306 (p : Pattern) (guard : d5502 p = 1) : d2672 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2672, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21305 p hg
    simpa only [d2672, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2672, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21261 p hg
    simpa only [d2672, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21307 (p : Pattern) (guard : d5502 p = 1) : d2673 p ≤ (0 : Int) + d2991 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2673, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21306 p hg
    simpa only [d2673, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2673, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21283 p hg
    simpa only [d2673, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21308 (p : Pattern) (guard : d5502 p = 1) : d2674 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2674, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21301 p hg
    simpa only [d2674, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2674, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21307 p hg
    simpa only [d2674, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21309 (p : Pattern) (guard : d5502 p = 1) : d2675 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21285 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21308 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21310 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21311 (p : Pattern) (guard : d5502 p = 1) : d2676 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21310 p hg
    simpa only [d5502, d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21312 (p : Pattern) (guard : d5502 p = 1) : d2677 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5749 p hg
    simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21313 (p : Pattern) (guard : d5502 p = 1) : d2678 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21311 p hg
    simpa only [d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21314 (p : Pattern) (guard : d5502 p = 1) : d2677 p ≤ (0 : Int) + d1941 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2677, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2677, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2677, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19595 p hg
    simpa only [d5502, d2677, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21315 (p : Pattern) (guard : d5502 p = 1) : d2679 p ≤ (0 : Int) + d1940 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19595 p hg
    simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21316 (p : Pattern) (guard : d5502 p = 1) : d2680 p ≤ (0 : Int) + d1942 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2680, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21314 p hg
    simpa only [d2680, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2680, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21315 p hg
    simpa only [d2680, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21317 (p : Pattern) (guard : d5502 p = 1) : d2681 p ≤ (0 : Int) + d2993 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2681, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21313 p hg
    simpa only [d2681, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2681, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21316 p hg
    simpa only [d2681, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21318 (p : Pattern) (guard : d5502 p = 1) : d2677 p ≤ (0 : Int) + d1874 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2677, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2677, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2677, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19598 p hg
    simpa only [d5502, d2677, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21319 (p : Pattern) (guard : d5502 p = 1) : d2682 p ≤ (0 : Int) + d1873 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17311 p hg
    simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19598 p hg
    simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21320 (p : Pattern) (guard : d5502 p = 1) : d2683 p ≤ (0 : Int) + d1875 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2683, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21318 p hg
    simpa only [d2683, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2683, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21319 p hg
    simpa only [d2683, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21321 (p : Pattern) (guard : d5502 p = 1) : d2684 p ≤ (0 : Int) + d1876 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2684, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21320 p hg
    simpa only [d2684, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2684, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2684, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21322 (p : Pattern) (guard : d5502 p = 1) : d2685 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2685, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21317 p hg
    simpa only [d2685, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2685, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21321 p hg
    simpa only [d2685, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21323 (p : Pattern) (guard : d5502 p = 1) : d2686 p ≤ (0 : Int) + d2993 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2686, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d2686, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2686, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21316 p hg
    simpa only [d2686, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21324 (p : Pattern) (guard : d5502 p = 1) : d2687 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2687, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21323 p hg
    simpa only [d2687, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2687, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21321 p hg
    simpa only [d2687, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21325 (p : Pattern) (guard : d5502 p = 1) : d2688 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21322 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21324 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21326 (p : Pattern) (guard : d5502 p = 1) : d2689 p ≤ (0 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5753 p hg
    simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21327 (p : Pattern) (guard : d5502 p = 1) : d2689 p ≤ (0 : Int) + d2129 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2689, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d5502, d2689, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2689, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19611 p hg
    simpa only [d5502, d2689, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21328 (p : Pattern) (guard : d5502 p = 1) : d2690 p ≤ (0 : Int) + d1964 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17408 p hg
    simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19611 p hg
    simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21329 (p : Pattern) (guard : d5502 p = 1) : d2691 p ≤ (0 : Int) + d2130 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2691, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21327 p hg
    simpa only [d2691, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2691, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21328 p hg
    simpa only [d2691, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21330 (p : Pattern) (guard : d5502 p = 1) : d2692 p ≤ (0 : Int) + d2995 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2692, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d2692, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2692, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21329 p hg
    simpa only [d2692, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21331 (p : Pattern) (guard : d5502 p = 1) : d2689 p ≤ (0 : Int) + d1882 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2689, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d5502, d2689, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2689, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19614 p hg
    simpa only [d5502, d2689, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21332 (p : Pattern) (guard : d5502 p = 1) : d2693 p ≤ (0 : Int) + d1881 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17324 p hg
    simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19614 p hg
    simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21333 (p : Pattern) (guard : d5502 p = 1) : d2694 p ≤ (0 : Int) + d1883 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2694, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21331 p hg
    simpa only [d2694, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2694, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21332 p hg
    simpa only [d2694, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21334 (p : Pattern) (guard : d5502 p = 1) : d2695 p ≤ (0 : Int) + d1884 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2695, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21333 p hg
    simpa only [d2695, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2695, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2695, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21335 (p : Pattern) (guard : d5502 p = 1) : d2696 p ≤ (0 : Int) + d2996 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2696, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21330 p hg
    simpa only [d2696, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2696, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21334 p hg
    simpa only [d2696, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21336 (p : Pattern) (guard : d5502 p = 1) : d2697 p ≤ (0 : Int) + d2997 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2697, d2997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21324 p hg
    simpa only [d2697, d2997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2697, d2997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21335 p hg
    simpa only [d2697, d2997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21337 (p : Pattern) (guard : d5502 p = 1) : d2698 p ≤ (0 : Int) + d2998 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2698, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21325 p hg
    simpa only [d2698, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2698, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21336 p hg
    simpa only [d2698, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21338 (p : Pattern) (guard : d5502 p = 1) : d2699 p ≤ (0 : Int) + d2999 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2699, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21196 p hg
    simpa only [d2699, d2999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2699, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2699, d2999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21339 (p : Pattern) (guard : d5502 p = 1) : d2700 p ≤ (0 : Int) + d3000 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2700, d3000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21336 p hg
    simpa only [d2700, d3000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2700, d3000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21338 p hg
    simpa only [d2700, d3000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21340 (p : Pattern) (guard : d5502 p = 1) : d2701 p ≤ (0 : Int) + d3001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2701, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21337 p hg
    simpa only [d2701, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2701, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21339 p hg
    simpa only [d2701, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21341 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1946 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21342 (p : Pattern) (guard : d5502 p = 1) : d2677 p ≤ (0 : Int) + d1947 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2677, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2677, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2677, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21341 p hg
    simpa only [d5502, d2677, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21343 (p : Pattern) (guard : d5502 p = 1) : d2679 p ≤ (0 : Int) + d1956 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2679, d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d2679, d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2679, d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20790 p hg
    simpa only [d5502, d2679, d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21344 (p : Pattern) (guard : d5502 p = 1) : d2680 p ≤ (0 : Int) + d1957 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2680, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21342 p hg
    simpa only [d2680, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2680, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21343 p hg
    simpa only [d2680, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21345 (p : Pattern) (guard : d5502 p = 1) : d2686 p ≤ (0 : Int) + d3002 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2686, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d2686, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2686, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21344 p hg
    simpa only [d2686, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21346 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1892 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21347 (p : Pattern) (guard : d5502 p = 1) : d2702 p ≤ (0 : Int) + d1893 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2702, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d5502, d2702, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2702, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21346 p hg
    simpa only [d5502, d2702, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21348 (p : Pattern) (guard : d5502 p = 1) : d2703 p ≤ (0 : Int) + d1897 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2703, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d5502, d2703, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2703, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20798 p hg
    simpa only [d5502, d2703, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21349 (p : Pattern) (guard : d5502 p = 1) : d2704 p ≤ (0 : Int) + d1898 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2704, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21347 p hg
    simpa only [d2704, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2704, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21348 p hg
    simpa only [d2704, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21350 (p : Pattern) (guard : d5502 p = 1) : d2705 p ≤ (0 : Int) + d1899 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2705, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21349 p hg
    simpa only [d2705, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2705, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2705, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21351 (p : Pattern) (guard : d5502 p = 1) : d2706 p ≤ (0 : Int) + d3003 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2706, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21345 p hg
    simpa only [d2706, d3003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2706, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21350 p hg
    simpa only [d2706, d3003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21352 (p : Pattern) (guard : d5502 p = 1) : d2707 p ≤ (0 : Int) + d1901 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2707, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d5502, d2707, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2707, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20803 p hg
    simpa only [d5502, d2707, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21353 (p : Pattern) (guard : d5502 p = 1) : d2708 p ≤ (0 : Int) + d1904 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2708, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17344 p hg
    simpa only [d5502, d2708, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2708, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20803 p hg
    simpa only [d5502, d2708, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21354 (p : Pattern) (guard : d5502 p = 1) : d2709 p ≤ (0 : Int) + d1905 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2709, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21352 p hg
    simpa only [d2709, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2709, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21353 p hg
    simpa only [d2709, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21355 (p : Pattern) (guard : d5502 p = 1) : d2710 p ≤ (0 : Int) + d1906 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2710, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21354 p hg
    simpa only [d2710, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2710, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2710, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21356 (p : Pattern) (guard : d5502 p = 1) : d2711 p ≤ (0 : Int) + d3004 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2711, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21345 p hg
    simpa only [d2711, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2711, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21355 p hg
    simpa only [d2711, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21357 (p : Pattern) (guard : d5502 p = 1) : d2712 p ≤ (0 : Int) + d3005 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2712, d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21351 p hg
    simpa only [d2712, d3005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2712, d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21356 p hg
    simpa only [d2712, d3005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21358 (p : Pattern) (guard : d5502 p = 1) : d2713 p ≤ (0 : Int) + d3006 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2713, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21345 p hg
    simpa only [d2713, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2713, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2713, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21359 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1961 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21360 (p : Pattern) (guard : d5502 p = 1) : d2689 p ≤ (0 : Int) + d1962 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2689, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d5502, d2689, d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2689, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21359 p hg
    simpa only [d5502, d2689, d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21361 (p : Pattern) (guard : d5502 p = 1) : d2690 p ≤ (0 : Int) + d1965 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2690, d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17408 p hg
    simpa only [d5502, d2690, d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2690, d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20815 p hg
    simpa only [d5502, d2690, d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21362 (p : Pattern) (guard : d5502 p = 1) : d2691 p ≤ (0 : Int) + d1966 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2691, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21360 p hg
    simpa only [d2691, d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2691, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21361 p hg
    simpa only [d2691, d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21363 (p : Pattern) (guard : d5502 p = 1) : d2692 p ≤ (0 : Int) + d3007 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2692, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d2692, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2692, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21362 p hg
    simpa only [d2692, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21364 (p : Pattern) (guard : d5502 p = 1) : d2714 p ≤ (0 : Int) + d3008 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2714, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21363 p hg
    simpa only [d2714, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2714, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2714, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21365 (p : Pattern) (guard : d5502 p = 1) : d2715 p ≤ (0 : Int) + d3009 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2715, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21358 p hg
    simpa only [d2715, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2715, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21364 p hg
    simpa only [d2715, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21366 (p : Pattern) (guard : d5502 p = 1) : d2716 p ≤ (0 : Int) + d3010 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2716, d3010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21357 p hg
    simpa only [d2716, d3010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2716, d3010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21365 p hg
    simpa only [d2716, d3010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21367 (p : Pattern) (guard : d5502 p = 1) : d2717 p ≤ (0 : Int) + d3011 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2717, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21209 p hg
    simpa only [d2717, d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2717, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2717, d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21368 (p : Pattern) (guard : d5502 p = 1) : d2718 p ≤ (0 : Int) + d3012 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2718, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21365 p hg
    simpa only [d2718, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2718, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21367 p hg
    simpa only [d2718, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21369 (p : Pattern) (guard : d5502 p = 1) : d2719 p ≤ (0 : Int) + d3013 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2719, d3013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21366 p hg
    simpa only [d2719, d3013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2719, d3013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21368 p hg
    simpa only [d2719, d3013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21370 (p : Pattern) (guard : d5502 p = 1) : d2720 p ≤ (0 : Int) + d3014 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2720, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21340 p hg
    simpa only [d2720, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2720, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21369 p hg
    simpa only [d2720, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21371 (p : Pattern) (guard : d0 p = 1) : d327 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21372 (p : Pattern) (guard : d5502 p = 1) : d2721 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21371 p hg
    simpa only [d5502, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21373 (p : Pattern) (guard : d5502 p = 1) : d2722 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21372 p hg
    simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21374 (p : Pattern) (guard : d5502 p = 1) : d2723 p ≤ (0 : Int) + d2993 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2723, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21373 p hg
    simpa only [d2723, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2723, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21316 p hg
    simpa only [d2723, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21375 (p : Pattern) (guard : d5502 p = 1) : d2724 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2724, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21374 p hg
    simpa only [d2724, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2724, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21321 p hg
    simpa only [d2724, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21376 (p : Pattern) (guard : d5502 p = 1) : d2702 p ≤ (0 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5764 p hg
    simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21377 (p : Pattern) (guard : d5502 p = 1) : d2702 p ≤ (0 : Int) + d2124 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2702, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d5502, d2702, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2702, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19624 p hg
    simpa only [d5502, d2702, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21378 (p : Pattern) (guard : d5502 p = 1) : d2703 p ≤ (0 : Int) + d1895 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19624 p hg
    simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21379 (p : Pattern) (guard : d5502 p = 1) : d2704 p ≤ (0 : Int) + d2125 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2704, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21377 p hg
    simpa only [d2704, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2704, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21378 p hg
    simpa only [d2704, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21380 (p : Pattern) (guard : d5502 p = 1) : d2725 p ≤ (0 : Int) + d3015 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2725, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d2725, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2725, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21379 p hg
    simpa only [d2725, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21381 (p : Pattern) (guard : d5502 p = 1) : d2702 p ≤ (0 : Int) + d1920 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2702, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d5502, d2702, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2702, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19647 p hg
    simpa only [d5502, d2702, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21382 (p : Pattern) (guard : d5502 p = 1) : d2726 p ≤ (0 : Int) + d1919 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17366 p hg
    simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19647 p hg
    simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21383 (p : Pattern) (guard : d5502 p = 1) : d2727 p ≤ (0 : Int) + d1921 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2727, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21381 p hg
    simpa only [d2727, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2727, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21382 p hg
    simpa only [d2727, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21384 (p : Pattern) (guard : d5502 p = 1) : d2728 p ≤ (0 : Int) + d1922 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2728, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21383 p hg
    simpa only [d2728, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2728, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2728, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21385 (p : Pattern) (guard : d5502 p = 1) : d2729 p ≤ (0 : Int) + d3016 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2729, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21380 p hg
    simpa only [d2729, d3016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2729, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21384 p hg
    simpa only [d2729, d3016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21386 (p : Pattern) (guard : d5502 p = 1) : d2730 p ≤ (0 : Int) + d3017 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2730, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21375 p hg
    simpa only [d2730, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2730, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21385 p hg
    simpa only [d2730, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21387 (p : Pattern) (guard : d5502 p = 1) : d2731 p ≤ (0 : Int) + d3018 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2731, d3018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21335 p hg
    simpa only [d2731, d3018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2731, d3018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21196 p hg
    simpa only [d2731, d3018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21388 (p : Pattern) (guard : d5502 p = 1) : d2732 p ≤ (0 : Int) + d3019 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2732, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21386 p hg
    simpa only [d2732, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2732, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21387 p hg
    simpa only [d2732, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21389 (p : Pattern) (guard : d5502 p = 1) : d2733 p ≤ (0 : Int) + d3020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2733, d3020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21335 p hg
    simpa only [d2733, d3020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2733, d3020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21200 p hg
    simpa only [d2733, d3020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21390 (p : Pattern) (guard : d5502 p = 1) : d2734 p ≤ (0 : Int) + d3021 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2734, d3021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21389 p hg
    simpa only [d2734, d3021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2734, d3021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2734, d3021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21391 (p : Pattern) (guard : d5502 p = 1) : d2735 p ≤ (0 : Int) + d3022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2735, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21388 p hg
    simpa only [d2735, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2735, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21390 p hg
    simpa only [d2735, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21392 (p : Pattern) (guard : d5502 p = 1) : d2725 p ≤ (0 : Int) + d3023 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2725, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d2725, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2725, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21349 p hg
    simpa only [d2725, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21393 (p : Pattern) (guard : d5502 p = 1) : d2736 p ≤ (0 : Int) + d3024 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2736, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21392 p hg
    simpa only [d2736, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2736, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2736, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21394 (p : Pattern) (guard : d5502 p = 1) : d2737 p ≤ (0 : Int) + d3025 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2737, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21356 p hg
    simpa only [d2737, d3025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2737, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21393 p hg
    simpa only [d2737, d3025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21395 (p : Pattern) (guard : d5502 p = 1) : d2738 p ≤ (0 : Int) + d3026 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2738, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21364 p hg
    simpa only [d2738, d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2738, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21209 p hg
    simpa only [d2738, d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21396 (p : Pattern) (guard : d5502 p = 1) : d2739 p ≤ (0 : Int) + d3027 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2739, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21394 p hg
    simpa only [d2739, d3027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2739, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21395 p hg
    simpa only [d2739, d3027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21397 (p : Pattern) (guard : d5502 p = 1) : d2740 p ≤ (0 : Int) + d3028 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2740, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21364 p hg
    simpa only [d2740, d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2740, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21211 p hg
    simpa only [d2740, d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21398 (p : Pattern) (guard : d5502 p = 1) : d2741 p ≤ (0 : Int) + d3029 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2741, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21397 p hg
    simpa only [d2741, d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2741, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2741, d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21399 (p : Pattern) (guard : d5502 p = 1) : d2742 p ≤ (0 : Int) + d3030 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2742, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21396 p hg
    simpa only [d2742, d3030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2742, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21398 p hg
    simpa only [d2742, d3030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21400 (p : Pattern) (guard : d5502 p = 1) : d2743 p ≤ (0 : Int) + d3031 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2743, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21391 p hg
    simpa only [d2743, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2743, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21399 p hg
    simpa only [d2743, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21401 (p : Pattern) (guard : d5502 p = 1) : d2744 p ≤ (0 : Int) + d3032 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2744, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21370 p hg
    simpa only [d2744, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2744, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21400 p hg
    simpa only [d2744, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21402 (p : Pattern) (guard : d5502 p = 1) : d2679 p ≤ (0 : Int) + d2107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2679, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d2679, d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2679, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21341 p hg
    simpa only [d5502, d2679, d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21403 (p : Pattern) (guard : d5502 p = 1) : d2680 p ≤ (0 : Int) + d2108 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2680, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21342 p hg
    simpa only [d2680, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2680, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21402 p hg
    simpa only [d2680, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21404 (p : Pattern) (guard : d5502 p = 1) : d2686 p ≤ (0 : Int) + d3033 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2686, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d2686, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2686, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21403 p hg
    simpa only [d2686, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21405 (p : Pattern) (guard : d5502 p = 1) : d2745 p ≤ (0 : Int) + d1943 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2745, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21316 p hg
    simpa only [d2745, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2745, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2745, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21406 (p : Pattern) (guard : d5502 p = 1) : d2746 p ≤ (0 : Int) + d3034 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2746, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21404 p hg
    simpa only [d2746, d3034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2746, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21405 p hg
    simpa only [d2746, d3034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21407 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3036 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21408 (p : Pattern) (guard : d5502 p = 1) : d2679 p ≤ (0 : Int) + d3037 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2679, d3037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d2679, d3037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2679, d3037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21407 p hg
    simpa only [d5502, d2679, d3037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21409 (p : Pattern) (guard : d5502 p = 1) : d2680 p ≤ (0 : Int) + d3038 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2680, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21342 p hg
    simpa only [d2680, d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2680, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21408 p hg
    simpa only [d2680, d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21410 (p : Pattern) (guard : d5502 p = 1) : d2686 p ≤ (0 : Int) + d3039 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2686, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d2686, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2686, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21409 p hg
    simpa only [d2686, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21411 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1949 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21412 (p : Pattern) (guard : d5502 p = 1) : d2679 p ≤ (0 : Int) + d1950 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2679, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d2679, d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2679, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21411 p hg
    simpa only [d5502, d2679, d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21413 (p : Pattern) (guard : d5502 p = 1) : d2680 p ≤ (0 : Int) + d1951 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2680, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21342 p hg
    simpa only [d2680, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2680, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21412 p hg
    simpa only [d2680, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21414 (p : Pattern) (guard : d5502 p = 1) : d2745 p ≤ (0 : Int) + d1952 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2745, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21413 p hg
    simpa only [d2745, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2745, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2745, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21415 (p : Pattern) (guard : d5502 p = 1) : d2746 p ≤ (0 : Int) + d3040 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2746, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21410 p hg
    simpa only [d2746, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2746, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21414 p hg
    simpa only [d2746, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21416 (p : Pattern) (guard : d5502 p = 1) : d2746 p ≤ (0 : Int) + d3041 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21406 p hg
    simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21415 p hg
    simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21417 (p : Pattern) (guard : d5502 p = 1) : d2745 p ≤ (0 : Int) + d1958 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2745, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21344 p hg
    simpa only [d2745, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2745, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2745, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21418 (p : Pattern) (guard : d5502 p = 1) : d2746 p ≤ (0 : Int) + d3042 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2746, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21345 p hg
    simpa only [d2746, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2746, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21417 p hg
    simpa only [d2746, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21419 (p : Pattern) (guard : d5502 p = 1) : d2747 p ≤ (0 : Int) + d1967 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2747, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21362 p hg
    simpa only [d2747, d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2747, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2747, d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
