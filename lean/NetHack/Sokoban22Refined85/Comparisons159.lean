/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons158
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22260 (p : Pattern) (guard : d5538 p = 1) : d2643 p ≤ (4 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2643, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22259 p hg
    simpa only [d2643, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2643, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22164 p hg
    simpa only [d2643, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22261 (p : Pattern) (guard : d5538 p = 1) : d2644 p ≤ (4 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2644, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22090 p hg
    simpa only [d2644, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2644, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22178 p hg
    simpa only [d2644, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22262 (p : Pattern) (guard : d5538 p = 1) : d2645 p ≤ (4 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2645, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22261 p hg
    simpa only [d2645, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2645, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22180 p hg
    simpa only [d2645, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22263 (p : Pattern) (guard : d5538 p = 1) : d2646 p ≤ (4 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2646, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22262 p hg
    simpa only [d2646, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2646, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22200 p hg
    simpa only [d2646, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22264 (p : Pattern) (guard : d5538 p = 1) : d2647 p ≤ (4 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2647, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22263 p hg
    simpa only [d2647, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2647, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22211 p hg
    simpa only [d2647, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22265 (p : Pattern) (guard : d5538 p = 1) : d2648 p ≤ (4 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2648, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22260 p hg
    simpa only [d2648, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2648, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22264 p hg
    simpa only [d2648, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22266 (p : Pattern) (guard : d5538 p = 1) : d2649 p ≤ (4 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2649, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22265 p hg
    simpa only [d2649, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2649, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22245 p hg
    simpa only [d2649, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22267 (p : Pattern) (guard : d5538 p = 1) : d2650 p ≤ (4 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2650, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22245 p hg
    simpa only [d2650, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2650, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2650, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22268 (p : Pattern) (guard : d5538 p = 1) : d2651 p ≤ (4 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2651, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22266 p hg
    simpa only [d2651, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2651, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22267 p hg
    simpa only [d2651, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22269 (p : Pattern) (guard : d5538 p = 1) : d2652 p ≤ (4 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2652, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22256 p hg
    simpa only [d2652, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2652, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22268 p hg
    simpa only [d2652, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22270 (p : Pattern) (guard : d0 p = 1) : d2653 p ≤ (4 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22271 (p : Pattern) (guard : d5538 p = 1) : d2654 p ≤ (4 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22270 p hg
    simpa only [d5538, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22067 p hg
    simpa only [d5538, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22272 (p : Pattern) (guard : d5538 p = 1) : d2655 p ≤ (4 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22271 p hg
    simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22074 p hg
    simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22273 (p : Pattern) (guard : d5538 p = 1) : d2656 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2656, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22272 p hg
    simpa only [d2656, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2656, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22081 p hg
    simpa only [d2656, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22274 (p : Pattern) (guard : d5538 p = 1) : d2657 p ≤ (4 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22273 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22090 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22275 (p : Pattern) (guard : d5538 p = 1) : d2658 p ≤ (4 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2658, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22274 p hg
    simpa only [d2658, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2658, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22107 p hg
    simpa only [d2658, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22276 (p : Pattern) (guard : d5538 p = 1) : d2659 p ≤ (4 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2659, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22275 p hg
    simpa only [d2659, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2659, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22126 p hg
    simpa only [d2659, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22277 (p : Pattern) (guard : d5538 p = 1) : d2660 p ≤ (4 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2660, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22276 p hg
    simpa only [d2660, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2660, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22164 p hg
    simpa only [d2660, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22278 (p : Pattern) (guard : d5538 p = 1) : d2661 p ≤ (4 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2661, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22086 p hg
    simpa only [d2661, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2661, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22178 p hg
    simpa only [d2661, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22279 (p : Pattern) (guard : d5538 p = 1) : d2662 p ≤ (4 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2662, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22278 p hg
    simpa only [d2662, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2662, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22180 p hg
    simpa only [d2662, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22280 (p : Pattern) (guard : d5538 p = 1) : d2663 p ≤ (4 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2663, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22279 p hg
    simpa only [d2663, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2663, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22200 p hg
    simpa only [d2663, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22281 (p : Pattern) (guard : d5538 p = 1) : d2664 p ≤ (4 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2664, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22280 p hg
    simpa only [d2664, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2664, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22211 p hg
    simpa only [d2664, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22282 (p : Pattern) (guard : d5538 p = 1) : d2665 p ≤ (4 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2665, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22277 p hg
    simpa only [d2665, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2665, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22281 p hg
    simpa only [d2665, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22283 (p : Pattern) (guard : d5538 p = 1) : d2666 p ≤ (4 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2666, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22282 p hg
    simpa only [d2666, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2666, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22245 p hg
    simpa only [d2666, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22284 (p : Pattern) (guard : d5538 p = 1) : d2667 p ≤ (4 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2667, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22283 p hg
    simpa only [d2667, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2667, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22255 p hg
    simpa only [d2667, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22285 (p : Pattern) (guard : d5538 p = 1) : d2668 p ≤ (4 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2668, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22090 p hg
    simpa only [d2668, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2668, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22107 p hg
    simpa only [d2668, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22286 (p : Pattern) (guard : d5538 p = 1) : d2669 p ≤ (4 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2669, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22285 p hg
    simpa only [d2669, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2669, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22126 p hg
    simpa only [d2669, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22287 (p : Pattern) (guard : d5538 p = 1) : d2670 p ≤ (4 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2670, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22286 p hg
    simpa only [d2670, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2670, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22164 p hg
    simpa only [d2670, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22288 (p : Pattern) (guard : d5538 p = 1) : d2671 p ≤ (4 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2671, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22287 p hg
    simpa only [d2671, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2671, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22264 p hg
    simpa only [d2671, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22289 (p : Pattern) (guard : d5538 p = 1) : d2672 p ≤ (4 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2672, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22288 p hg
    simpa only [d2672, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2672, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22245 p hg
    simpa only [d2672, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22290 (p : Pattern) (guard : d5538 p = 1) : d2673 p ≤ (4 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2673, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22289 p hg
    simpa only [d2673, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2673, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22267 p hg
    simpa only [d2673, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22291 (p : Pattern) (guard : d5538 p = 1) : d2674 p ≤ (4 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2674, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22284 p hg
    simpa only [d2674, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2674, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22290 p hg
    simpa only [d2674, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22292 (p : Pattern) (guard : d5538 p = 1) : d2675 p ≤ (4 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22269 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22291 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22293 (p : Pattern) (guard : d0 p = 1) : d2676 p ≤ (4 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22294 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22295 (p : Pattern) (guard : d5502 p = 1) : d2677 p ≤ (4 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22294 p hg
    simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22296 (p : Pattern) (guard : d5538 p = 1) : d2678 p ≤ (4 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22293 p hg
    simpa only [d5538, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22295 p hg
    simpa only [d5538, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22297 (p : Pattern) (guard : d0 p = 1) : d2677 p ≤ (4 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22298 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (4 : Int) + d1 p := by
  omega
theorem compare22299 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (4 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22298 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2590 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22300 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (4 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22299 p hg
    simpa only [d1940, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2591 p hg
    simpa only [d1940, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22301 (p : Pattern) (guard : d5502 p = 1) : d2679 p ≤ (4 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22300 p hg
    simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22294 p hg
    simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22302 (p : Pattern) (guard : d5538 p = 1) : d2680 p ≤ (4 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22297 p hg
    simpa only [d5538, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22301 p hg
    simpa only [d5538, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22303 (p : Pattern) (guard : d5538 p = 1) : d2681 p ≤ (4 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22296 p hg
    simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22302 p hg
    simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22304 (p : Pattern) (guard : d1 p = 1) : d1872 p ≤ (4 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22298 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2716 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22305 (p : Pattern) (guard : d1 p = 1) : d1873 p ≤ (4 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1873, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22304 p hg
    simpa only [d1873, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1873, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2717 p hg
    simpa only [d1873, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22306 (p : Pattern) (guard : d5502 p = 1) : d2682 p ≤ (4 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22305 p hg
    simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22294 p hg
    simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22307 (p : Pattern) (guard : d5538 p = 1) : d2683 p ≤ (4 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22297 p hg
    simpa only [d5538, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22306 p hg
    simpa only [d5538, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22308 (p : Pattern) (guard : d5538 p = 1) : d2684 p ≤ (4 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2684, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22307 p hg
    simpa only [d2684, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2684, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2684, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22309 (p : Pattern) (guard : d5538 p = 1) : d2685 p ≤ (4 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2685, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22303 p hg
    simpa only [d2685, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2685, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22308 p hg
    simpa only [d2685, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22310 (p : Pattern) (guard : d5538 p = 1) : d2677 p ≤ (4 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22297 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22295 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22311 (p : Pattern) (guard : d5538 p = 1) : d2686 p ≤ (4 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22310 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22302 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22312 (p : Pattern) (guard : d5538 p = 1) : d2687 p ≤ (4 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2687, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22311 p hg
    simpa only [d2687, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2687, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22308 p hg
    simpa only [d2687, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22313 (p : Pattern) (guard : d5538 p = 1) : d2688 p ≤ (4 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22309 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22312 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22314 (p : Pattern) (guard : d0 p = 1) : d2689 p ≤ (4 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22315 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22316 (p : Pattern) (guard : d5502 p = 1) : d2689 p ≤ (4 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2606 p hg
    simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22315 p hg
    simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22317 (p : Pattern) (guard : d5538 p = 1) : d2689 p ≤ (4 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22314 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22316 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22318 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (4 : Int) + d5 p := by
  omega
theorem compare22319 (p : Pattern) (guard : d1 p = 1) : d1963 p ≤ (4 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22318 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2607 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22320 (p : Pattern) (guard : d1 p = 1) : d1964 p ≤ (4 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1964, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22319 p hg
    simpa only [d1964, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1964, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2608 p hg
    simpa only [d1964, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22321 (p : Pattern) (guard : d5502 p = 1) : d2690 p ≤ (4 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22320 p hg
    simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22315 p hg
    simpa only [d5502, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22322 (p : Pattern) (guard : d5538 p = 1) : d2691 p ≤ (4 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22314 p hg
    simpa only [d5538, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22321 p hg
    simpa only [d5538, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22323 (p : Pattern) (guard : d5538 p = 1) : d2692 p ≤ (4 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22317 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22322 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22324 (p : Pattern) (guard : d1 p = 1) : d1880 p ≤ (4 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22318 p hg
    simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2753 p hg
    simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22325 (p : Pattern) (guard : d1 p = 1) : d1881 p ≤ (4 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1881, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22324 p hg
    simpa only [d1881, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1881, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2754 p hg
    simpa only [d1881, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22326 (p : Pattern) (guard : d5502 p = 1) : d2693 p ≤ (4 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22325 p hg
    simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22315 p hg
    simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22327 (p : Pattern) (guard : d5538 p = 1) : d2694 p ≤ (4 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22314 p hg
    simpa only [d5538, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22326 p hg
    simpa only [d5538, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22328 (p : Pattern) (guard : d5538 p = 1) : d2695 p ≤ (4 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2695, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22327 p hg
    simpa only [d2695, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2695, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2695, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22329 (p : Pattern) (guard : d5538 p = 1) : d2696 p ≤ (4 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2696, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22323 p hg
    simpa only [d2696, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2696, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22328 p hg
    simpa only [d2696, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22330 (p : Pattern) (guard : d5538 p = 1) : d2697 p ≤ (4 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2697, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22312 p hg
    simpa only [d2697, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2697, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22329 p hg
    simpa only [d2697, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22331 (p : Pattern) (guard : d5538 p = 1) : d2698 p ≤ (4 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2698, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22313 p hg
    simpa only [d2698, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2698, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22330 p hg
    simpa only [d2698, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22332 (p : Pattern) (guard : d5538 p = 1) : d2699 p ≤ (4 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2699, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22193 p hg
    simpa only [d2699, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2699, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2699, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22333 (p : Pattern) (guard : d5538 p = 1) : d2700 p ≤ (4 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2700, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22330 p hg
    simpa only [d2700, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2700, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22332 p hg
    simpa only [d2700, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22334 (p : Pattern) (guard : d5538 p = 1) : d2701 p ≤ (4 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2701, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22331 p hg
    simpa only [d2701, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2701, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22333 p hg
    simpa only [d2701, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22335 (p : Pattern) (guard : d0 p = 1) : d2702 p ≤ (4 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22336 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (4 : Int) + d3 p := by
  omega
theorem compare22337 (p : Pattern) (guard : d1 p = 1) : d1894 p ≤ (4 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22336 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2594 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22338 (p : Pattern) (guard : d1 p = 1) : d1895 p ≤ (4 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1895, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22337 p hg
    simpa only [d1895, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1895, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2595 p hg
    simpa only [d1895, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22339 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22340 (p : Pattern) (guard : d5502 p = 1) : d2703 p ≤ (4 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22338 p hg
    simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22339 p hg
    simpa only [d5502, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22341 (p : Pattern) (guard : d5538 p = 1) : d2704 p ≤ (4 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22335 p hg
    simpa only [d5538, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22340 p hg
    simpa only [d5538, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22342 (p : Pattern) (guard : d5538 p = 1) : d2705 p ≤ (4 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2705, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22341 p hg
    simpa only [d2705, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2705, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2705, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22343 (p : Pattern) (guard : d5538 p = 1) : d2706 p ≤ (4 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2706, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22311 p hg
    simpa only [d2706, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2706, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22342 p hg
    simpa only [d2706, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22344 (p : Pattern) (guard : d0 p = 1) : d2707 p ≤ (4 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22345 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (4 : Int) + d7 p := by
  omega
theorem compare22346 (p : Pattern) (guard : d1 p = 1) : d1902 p ≤ (4 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22345 p hg
    simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2599 p hg
    simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22347 (p : Pattern) (guard : d1 p = 1) : d1903 p ≤ (4 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1903, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22346 p hg
    simpa only [d1903, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1903, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2600 p hg
    simpa only [d1903, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22348 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22349 (p : Pattern) (guard : d5502 p = 1) : d2708 p ≤ (4 : Int) + d120 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22347 p hg
    simpa only [d5502, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22348 p hg
    simpa only [d5502, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22350 (p : Pattern) (guard : d5538 p = 1) : d2709 p ≤ (4 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22344 p hg
    simpa only [d5538, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22349 p hg
    simpa only [d5538, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22351 (p : Pattern) (guard : d5538 p = 1) : d2710 p ≤ (4 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2710, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22350 p hg
    simpa only [d2710, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2710, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2710, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22352 (p : Pattern) (guard : d5538 p = 1) : d2711 p ≤ (4 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2711, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22311 p hg
    simpa only [d2711, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2711, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22351 p hg
    simpa only [d2711, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22353 (p : Pattern) (guard : d5538 p = 1) : d2712 p ≤ (4 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2712, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22343 p hg
    simpa only [d2712, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2712, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22352 p hg
    simpa only [d2712, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22354 (p : Pattern) (guard : d5538 p = 1) : d2713 p ≤ (4 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2713, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22311 p hg
    simpa only [d2713, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2713, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2713, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22355 (p : Pattern) (guard : d5538 p = 1) : d2714 p ≤ (4 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2714, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22323 p hg
    simpa only [d2714, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2714, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2714, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22356 (p : Pattern) (guard : d5538 p = 1) : d2715 p ≤ (4 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2715, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22354 p hg
    simpa only [d2715, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2715, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22355 p hg
    simpa only [d2715, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22357 (p : Pattern) (guard : d5538 p = 1) : d2716 p ≤ (4 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2716, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22353 p hg
    simpa only [d2716, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2716, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22356 p hg
    simpa only [d2716, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22358 (p : Pattern) (guard : d5538 p = 1) : d2717 p ≤ (4 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2717, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22206 p hg
    simpa only [d2717, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2717, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2717, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22359 (p : Pattern) (guard : d5538 p = 1) : d2718 p ≤ (4 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2718, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22356 p hg
    simpa only [d2718, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2718, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22358 p hg
    simpa only [d2718, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22360 (p : Pattern) (guard : d5538 p = 1) : d2719 p ≤ (4 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2719, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22357 p hg
    simpa only [d2719, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2719, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22359 p hg
    simpa only [d2719, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22361 (p : Pattern) (guard : d5538 p = 1) : d2720 p ≤ (4 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2720, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22334 p hg
    simpa only [d2720, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2720, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22360 p hg
    simpa only [d2720, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22362 (p : Pattern) (guard : d0 p = 1) : d2721 p ≤ (4 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22363 (p : Pattern) (guard : d5538 p = 1) : d2722 p ≤ (4 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22362 p hg
    simpa only [d5538, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22295 p hg
    simpa only [d5538, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22364 (p : Pattern) (guard : d5538 p = 1) : d2723 p ≤ (4 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22363 p hg
    simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22302 p hg
    simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22365 (p : Pattern) (guard : d5538 p = 1) : d2724 p ≤ (4 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2724, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22364 p hg
    simpa only [d2724, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2724, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22308 p hg
    simpa only [d2724, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22366 (p : Pattern) (guard : d5502 p = 1) : d2702 p ≤ (4 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22339 p hg
    simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22367 (p : Pattern) (guard : d5538 p = 1) : d2702 p ≤ (4 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22335 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22366 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22368 (p : Pattern) (guard : d5538 p = 1) : d2725 p ≤ (4 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22367 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22341 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22369 (p : Pattern) (guard : d1 p = 1) : d1918 p ≤ (4 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22336 p hg
    simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8521 p hg
    simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22370 (p : Pattern) (guard : d1 p = 1) : d1919 p ≤ (4 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1919, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22369 p hg
    simpa only [d1919, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1919, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8522 p hg
    simpa only [d1919, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22371 (p : Pattern) (guard : d5502 p = 1) : d2726 p ≤ (4 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22370 p hg
    simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22339 p hg
    simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22372 (p : Pattern) (guard : d5538 p = 1) : d2727 p ≤ (4 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22335 p hg
    simpa only [d5538, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22371 p hg
    simpa only [d5538, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22373 (p : Pattern) (guard : d5538 p = 1) : d2728 p ≤ (4 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2728, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22372 p hg
    simpa only [d2728, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2728, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2728, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22374 (p : Pattern) (guard : d5538 p = 1) : d2729 p ≤ (4 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2729, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22368 p hg
    simpa only [d2729, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2729, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22373 p hg
    simpa only [d2729, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22375 (p : Pattern) (guard : d5538 p = 1) : d2730 p ≤ (4 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2730, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22365 p hg
    simpa only [d2730, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2730, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22374 p hg
    simpa only [d2730, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22376 (p : Pattern) (guard : d5538 p = 1) : d2731 p ≤ (4 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2731, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22329 p hg
    simpa only [d2731, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2731, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22193 p hg
    simpa only [d2731, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22377 (p : Pattern) (guard : d5538 p = 1) : d2732 p ≤ (4 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2732, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22375 p hg
    simpa only [d2732, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2732, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22376 p hg
    simpa only [d2732, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22378 (p : Pattern) (guard : d5538 p = 1) : d2733 p ≤ (4 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2733, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22329 p hg
    simpa only [d2733, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2733, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d2733, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22379 (p : Pattern) (guard : d5538 p = 1) : d2734 p ≤ (4 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2734, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22378 p hg
    simpa only [d2734, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2734, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2734, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22380 (p : Pattern) (guard : d5538 p = 1) : d2735 p ≤ (4 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2735, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22377 p hg
    simpa only [d2735, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2735, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22379 p hg
    simpa only [d2735, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22381 (p : Pattern) (guard : d5538 p = 1) : d2736 p ≤ (4 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2736, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22368 p hg
    simpa only [d2736, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2736, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2736, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22382 (p : Pattern) (guard : d5538 p = 1) : d2737 p ≤ (4 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2737, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22352 p hg
    simpa only [d2737, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2737, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22381 p hg
    simpa only [d2737, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22383 (p : Pattern) (guard : d5538 p = 1) : d2738 p ≤ (4 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2738, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22355 p hg
    simpa only [d2738, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2738, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22206 p hg
    simpa only [d2738, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22384 (p : Pattern) (guard : d5538 p = 1) : d2739 p ≤ (4 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2739, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22382 p hg
    simpa only [d2739, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2739, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22383 p hg
    simpa only [d2739, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22385 (p : Pattern) (guard : d5538 p = 1) : d2740 p ≤ (4 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2740, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22355 p hg
    simpa only [d2740, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2740, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22208 p hg
    simpa only [d2740, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22386 (p : Pattern) (guard : d5538 p = 1) : d2741 p ≤ (4 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2741, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22385 p hg
    simpa only [d2741, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2741, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2741, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22387 (p : Pattern) (guard : d5538 p = 1) : d2742 p ≤ (4 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2742, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22384 p hg
    simpa only [d2742, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2742, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22386 p hg
    simpa only [d2742, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22388 (p : Pattern) (guard : d5538 p = 1) : d2743 p ≤ (4 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2743, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22380 p hg
    simpa only [d2743, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2743, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22387 p hg
    simpa only [d2743, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22389 (p : Pattern) (guard : d5538 p = 1) : d2744 p ≤ (4 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2744, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22361 p hg
    simpa only [d2744, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2744, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22388 p hg
    simpa only [d2744, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22390 (p : Pattern) (guard : d5538 p = 1) : d2745 p ≤ (4 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2745, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22302 p hg
    simpa only [d2745, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2745, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2745, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22391 (p : Pattern) (guard : d5538 p = 1) : d2746 p ≤ (4 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2746, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22311 p hg
    simpa only [d2746, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2746, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22390 p hg
    simpa only [d2746, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22392 (p : Pattern) (guard : d5538 p = 1) : d2747 p ≤ (4 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2747, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22322 p hg
    simpa only [d2747, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2747, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2747, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22393 (p : Pattern) (guard : d5538 p = 1) : d2748 p ≤ (4 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2748, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22323 p hg
    simpa only [d2748, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2748, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22392 p hg
    simpa only [d2748, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22394 (p : Pattern) (guard : d5538 p = 1) : d2749 p ≤ (4 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2749, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22391 p hg
    simpa only [d2749, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2749, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22393 p hg
    simpa only [d2749, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22395 (p : Pattern) (guard : d5538 p = 1) : d2750 p ≤ (4 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2750, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22391 p hg
    simpa only [d2750, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2750, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22394 p hg
    simpa only [d2750, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22396 (p : Pattern) (guard : d5538 p = 1) : d2751 p ≤ (4 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2751, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22394 p hg
    simpa only [d2751, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2751, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22332 p hg
    simpa only [d2751, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22397 (p : Pattern) (guard : d5538 p = 1) : d2752 p ≤ (4 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2752, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22395 p hg
    simpa only [d2752, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2752, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22396 p hg
    simpa only [d2752, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22398 (p : Pattern) (guard : d5538 p = 1) : d2753 p ≤ (4 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2753, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22368 p hg
    simpa only [d2753, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2753, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22342 p hg
    simpa only [d2753, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22399 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (4 : Int) + d120 p := by
  omega
end NetHack.Sokoban22Refined85
