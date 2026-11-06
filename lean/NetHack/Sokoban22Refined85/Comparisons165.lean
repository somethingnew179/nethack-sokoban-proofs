/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons164
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23100 (p : Pattern) (guard : d5503 p = 1) : d2636 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2636, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23098 p hg
    simpa only [d2636, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2636, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2636, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23101 (p : Pattern) (guard : d5503 p = 1) : d2637 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2637, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23099 p hg
    simpa only [d2637, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2637, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23100 p hg
    simpa only [d2637, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23102 (p : Pattern) (guard : d5503 p = 1) : d2638 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2638, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23092 p hg
    simpa only [d2638, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2638, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23101 p hg
    simpa only [d2638, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23103 (p : Pattern) (guard : d5503 p = 1) : d2639 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2639, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23093 p hg
    simpa only [d2639, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2639, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23102 p hg
    simpa only [d2639, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23104 (p : Pattern) (guard : d5503 p = 1) : d2640 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22971 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22975 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23105 (p : Pattern) (guard : d5503 p = 1) : d2641 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2641, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23104 p hg
    simpa only [d2641, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2641, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22985 p hg
    simpa only [d2641, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23106 (p : Pattern) (guard : d5503 p = 1) : d2642 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2642, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23105 p hg
    simpa only [d2642, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2642, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22997 p hg
    simpa only [d2642, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23107 (p : Pattern) (guard : d5503 p = 1) : d2643 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2643, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23106 p hg
    simpa only [d2643, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2643, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23020 p hg
    simpa only [d2643, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23108 (p : Pattern) (guard : d5503 p = 1) : d2644 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2644, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22975 p hg
    simpa only [d2644, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2644, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23031 p hg
    simpa only [d2644, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23109 (p : Pattern) (guard : d5503 p = 1) : d2645 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2645, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23108 p hg
    simpa only [d2645, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2645, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23033 p hg
    simpa only [d2645, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23110 (p : Pattern) (guard : d5503 p = 1) : d2646 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2646, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23109 p hg
    simpa only [d2646, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2646, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23048 p hg
    simpa only [d2646, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23111 (p : Pattern) (guard : d5503 p = 1) : d2647 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2647, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23110 p hg
    simpa only [d2647, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2647, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23059 p hg
    simpa only [d2647, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23112 (p : Pattern) (guard : d5503 p = 1) : d2648 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2648, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23107 p hg
    simpa only [d2648, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2648, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23111 p hg
    simpa only [d2648, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23113 (p : Pattern) (guard : d5503 p = 1) : d2649 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2649, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23112 p hg
    simpa only [d2649, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2649, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23092 p hg
    simpa only [d2649, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23114 (p : Pattern) (guard : d5503 p = 1) : d2650 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2650, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23092 p hg
    simpa only [d2650, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2650, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2650, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23115 (p : Pattern) (guard : d5503 p = 1) : d2651 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2651, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23113 p hg
    simpa only [d2651, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2651, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23114 p hg
    simpa only [d2651, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23116 (p : Pattern) (guard : d5503 p = 1) : d2652 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2652, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23103 p hg
    simpa only [d2652, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2652, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23115 p hg
    simpa only [d2652, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23117 (p : Pattern) (guard : d5503 p = 1) : d2654 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21287 p hg
    simpa only [d5503, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22960 p hg
    simpa only [d5503, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23118 (p : Pattern) (guard : d5503 p = 1) : d2655 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23117 p hg
    simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22963 p hg
    simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23119 (p : Pattern) (guard : d5503 p = 1) : d2656 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2656, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23118 p hg
    simpa only [d2656, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2656, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22967 p hg
    simpa only [d2656, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23120 (p : Pattern) (guard : d5503 p = 1) : d2657 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23119 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22975 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23121 (p : Pattern) (guard : d5503 p = 1) : d2658 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2658, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23120 p hg
    simpa only [d2658, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2658, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22985 p hg
    simpa only [d2658, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23122 (p : Pattern) (guard : d5503 p = 1) : d2659 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2659, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23121 p hg
    simpa only [d2659, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2659, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22997 p hg
    simpa only [d2659, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23123 (p : Pattern) (guard : d5503 p = 1) : d2660 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2660, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23122 p hg
    simpa only [d2660, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2660, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23020 p hg
    simpa only [d2660, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23124 (p : Pattern) (guard : d5503 p = 1) : d2661 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2661, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22971 p hg
    simpa only [d2661, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2661, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23031 p hg
    simpa only [d2661, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23125 (p : Pattern) (guard : d5503 p = 1) : d2662 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2662, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23124 p hg
    simpa only [d2662, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2662, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23033 p hg
    simpa only [d2662, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23126 (p : Pattern) (guard : d5503 p = 1) : d2663 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2663, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23125 p hg
    simpa only [d2663, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2663, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23048 p hg
    simpa only [d2663, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23127 (p : Pattern) (guard : d5503 p = 1) : d2664 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2664, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23126 p hg
    simpa only [d2664, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2664, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23059 p hg
    simpa only [d2664, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23128 (p : Pattern) (guard : d5503 p = 1) : d2665 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2665, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23123 p hg
    simpa only [d2665, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2665, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23127 p hg
    simpa only [d2665, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23129 (p : Pattern) (guard : d5503 p = 1) : d2666 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2666, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23128 p hg
    simpa only [d2666, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2666, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23092 p hg
    simpa only [d2666, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23130 (p : Pattern) (guard : d5503 p = 1) : d2667 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2667, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23129 p hg
    simpa only [d2667, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2667, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23102 p hg
    simpa only [d2667, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23131 (p : Pattern) (guard : d5503 p = 1) : d2668 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2668, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22975 p hg
    simpa only [d2668, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2668, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22985 p hg
    simpa only [d2668, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23132 (p : Pattern) (guard : d5503 p = 1) : d2669 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2669, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23131 p hg
    simpa only [d2669, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2669, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22997 p hg
    simpa only [d2669, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23133 (p : Pattern) (guard : d5503 p = 1) : d2670 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2670, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23132 p hg
    simpa only [d2670, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2670, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23020 p hg
    simpa only [d2670, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23134 (p : Pattern) (guard : d5503 p = 1) : d2671 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2671, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23133 p hg
    simpa only [d2671, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2671, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23111 p hg
    simpa only [d2671, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23135 (p : Pattern) (guard : d5503 p = 1) : d2672 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2672, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23134 p hg
    simpa only [d2672, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2672, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23092 p hg
    simpa only [d2672, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23136 (p : Pattern) (guard : d5503 p = 1) : d2673 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2673, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23135 p hg
    simpa only [d2673, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2673, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23114 p hg
    simpa only [d2673, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23137 (p : Pattern) (guard : d5503 p = 1) : d2674 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2674, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23130 p hg
    simpa only [d2674, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2674, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23136 p hg
    simpa only [d2674, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23138 (p : Pattern) (guard : d5503 p = 1) : d2675 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23116 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23137 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23139 (p : Pattern) (guard : d0 p = 1) : d2677 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23140 (p : Pattern) (guard : d5503 p = 1) : d2678 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21311 p hg
    simpa only [d5503, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23139 p hg
    simpa only [d5503, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23141 (p : Pattern) (guard : d0 p = 1) : d2679 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23142 (p : Pattern) (guard : d5503 p = 1) : d2680 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d5503, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23141 p hg
    simpa only [d5503, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23143 (p : Pattern) (guard : d5503 p = 1) : d2681 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23140 p hg
    simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23142 p hg
    simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23144 (p : Pattern) (guard : d0 p = 1) : d2682 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23145 (p : Pattern) (guard : d5503 p = 1) : d2683 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d5503, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23144 p hg
    simpa only [d5503, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23146 (p : Pattern) (guard : d5503 p = 1) : d2684 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2684, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23145 p hg
    simpa only [d2684, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2684, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2684, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23147 (p : Pattern) (guard : d5503 p = 1) : d2685 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2685, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23143 p hg
    simpa only [d2685, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2685, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23146 p hg
    simpa only [d2685, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23148 (p : Pattern) (guard : d5503 p = 1) : d2677 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23139 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23149 (p : Pattern) (guard : d5503 p = 1) : d2686 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23148 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23142 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23150 (p : Pattern) (guard : d5503 p = 1) : d2687 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2687, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23149 p hg
    simpa only [d2687, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2687, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23146 p hg
    simpa only [d2687, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23151 (p : Pattern) (guard : d5503 p = 1) : d2688 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23147 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23150 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23152 (p : Pattern) (guard : d0 p = 1) : d2689 p ≤ (0 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23153 (p : Pattern) (guard : d5503 p = 1) : d2689 p ≤ (0 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23152 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23154 (p : Pattern) (guard : d0 p = 1) : d2690 p ≤ (0 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23155 (p : Pattern) (guard : d5503 p = 1) : d2691 p ≤ (0 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d5503, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23154 p hg
    simpa only [d5503, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23156 (p : Pattern) (guard : d5503 p = 1) : d2692 p ≤ (0 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23153 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23155 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23157 (p : Pattern) (guard : d0 p = 1) : d2693 p ≤ (0 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23158 (p : Pattern) (guard : d5503 p = 1) : d2694 p ≤ (0 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d5503, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23157 p hg
    simpa only [d5503, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23159 (p : Pattern) (guard : d5503 p = 1) : d2695 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2695, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23158 p hg
    simpa only [d2695, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2695, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2695, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23160 (p : Pattern) (guard : d5503 p = 1) : d2696 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2696, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23156 p hg
    simpa only [d2696, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2696, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23159 p hg
    simpa only [d2696, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23161 (p : Pattern) (guard : d5503 p = 1) : d2697 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2697, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23150 p hg
    simpa only [d2697, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2697, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23160 p hg
    simpa only [d2697, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23162 (p : Pattern) (guard : d5503 p = 1) : d2698 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2698, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23151 p hg
    simpa only [d2698, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2698, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23161 p hg
    simpa only [d2698, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23163 (p : Pattern) (guard : d5503 p = 1) : d2699 p ≤ (0 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2699, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23041 p hg
    simpa only [d2699, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2699, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2699, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23164 (p : Pattern) (guard : d5503 p = 1) : d2700 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2700, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23161 p hg
    simpa only [d2700, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2700, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23163 p hg
    simpa only [d2700, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23165 (p : Pattern) (guard : d5503 p = 1) : d2701 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2701, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23162 p hg
    simpa only [d2701, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2701, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23164 p hg
    simpa only [d2701, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23166 (p : Pattern) (guard : d0 p = 1) : d2703 p ≤ (0 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23167 (p : Pattern) (guard : d5503 p = 1) : d2704 p ≤ (0 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d5503, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23166 p hg
    simpa only [d5503, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23168 (p : Pattern) (guard : d5503 p = 1) : d2705 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2705, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23167 p hg
    simpa only [d2705, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2705, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2705, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23169 (p : Pattern) (guard : d5503 p = 1) : d2706 p ≤ (0 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2706, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23149 p hg
    simpa only [d2706, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2706, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23168 p hg
    simpa only [d2706, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23170 (p : Pattern) (guard : d0 p = 1) : d2708 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23171 (p : Pattern) (guard : d5503 p = 1) : d2709 p ≤ (0 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21426 p hg
    simpa only [d5503, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23170 p hg
    simpa only [d5503, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23172 (p : Pattern) (guard : d5503 p = 1) : d2710 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2710, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23171 p hg
    simpa only [d2710, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2710, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2710, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23173 (p : Pattern) (guard : d5503 p = 1) : d2711 p ≤ (0 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2711, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23149 p hg
    simpa only [d2711, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2711, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23172 p hg
    simpa only [d2711, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23174 (p : Pattern) (guard : d5503 p = 1) : d2712 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2712, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23169 p hg
    simpa only [d2712, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2712, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23173 p hg
    simpa only [d2712, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23175 (p : Pattern) (guard : d5503 p = 1) : d2713 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2713, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23149 p hg
    simpa only [d2713, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2713, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2713, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23176 (p : Pattern) (guard : d5503 p = 1) : d2714 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2714, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23156 p hg
    simpa only [d2714, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2714, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2714, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23177 (p : Pattern) (guard : d5503 p = 1) : d2715 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2715, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23175 p hg
    simpa only [d2715, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2715, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23176 p hg
    simpa only [d2715, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23178 (p : Pattern) (guard : d5503 p = 1) : d2716 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2716, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23174 p hg
    simpa only [d2716, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2716, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23177 p hg
    simpa only [d2716, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23179 (p : Pattern) (guard : d5503 p = 1) : d2717 p ≤ (0 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2717, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23054 p hg
    simpa only [d2717, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2717, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2717, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23180 (p : Pattern) (guard : d5503 p = 1) : d2718 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2718, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23177 p hg
    simpa only [d2718, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2718, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23179 p hg
    simpa only [d2718, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23181 (p : Pattern) (guard : d5503 p = 1) : d2719 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2719, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23178 p hg
    simpa only [d2719, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2719, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23180 p hg
    simpa only [d2719, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23182 (p : Pattern) (guard : d5503 p = 1) : d2720 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2720, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23165 p hg
    simpa only [d2720, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2720, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23181 p hg
    simpa only [d2720, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23183 (p : Pattern) (guard : d5503 p = 1) : d2722 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21372 p hg
    simpa only [d5503, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23139 p hg
    simpa only [d5503, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23184 (p : Pattern) (guard : d5503 p = 1) : d2723 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23183 p hg
    simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23142 p hg
    simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23185 (p : Pattern) (guard : d5503 p = 1) : d2724 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2724, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23184 p hg
    simpa only [d2724, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2724, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23146 p hg
    simpa only [d2724, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23186 (p : Pattern) (guard : d0 p = 1) : d2702 p ≤ (0 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23187 (p : Pattern) (guard : d5503 p = 1) : d2702 p ≤ (0 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23186 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23188 (p : Pattern) (guard : d5503 p = 1) : d2725 p ≤ (0 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23187 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23167 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23189 (p : Pattern) (guard : d0 p = 1) : d2726 p ≤ (0 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23190 (p : Pattern) (guard : d5503 p = 1) : d2727 p ≤ (0 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d5503, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23189 p hg
    simpa only [d5503, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23191 (p : Pattern) (guard : d5503 p = 1) : d2728 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2728, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23190 p hg
    simpa only [d2728, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2728, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2728, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23192 (p : Pattern) (guard : d5503 p = 1) : d2729 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2729, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23188 p hg
    simpa only [d2729, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2729, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23191 p hg
    simpa only [d2729, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23193 (p : Pattern) (guard : d5503 p = 1) : d2730 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2730, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23185 p hg
    simpa only [d2730, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2730, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23192 p hg
    simpa only [d2730, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23194 (p : Pattern) (guard : d5503 p = 1) : d2731 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2731, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23160 p hg
    simpa only [d2731, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2731, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23041 p hg
    simpa only [d2731, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23195 (p : Pattern) (guard : d5503 p = 1) : d2732 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2732, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23193 p hg
    simpa only [d2732, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2732, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23194 p hg
    simpa only [d2732, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23196 (p : Pattern) (guard : d5503 p = 1) : d2733 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2733, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23160 p hg
    simpa only [d2733, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2733, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23046 p hg
    simpa only [d2733, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23197 (p : Pattern) (guard : d5503 p = 1) : d2734 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2734, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23196 p hg
    simpa only [d2734, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2734, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2734, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23198 (p : Pattern) (guard : d5503 p = 1) : d2735 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2735, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23195 p hg
    simpa only [d2735, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2735, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23197 p hg
    simpa only [d2735, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23199 (p : Pattern) (guard : d5503 p = 1) : d2736 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2736, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23188 p hg
    simpa only [d2736, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2736, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2736, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23200 (p : Pattern) (guard : d5503 p = 1) : d2737 p ≤ (0 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2737, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23173 p hg
    simpa only [d2737, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2737, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23199 p hg
    simpa only [d2737, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23201 (p : Pattern) (guard : d5503 p = 1) : d2738 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2738, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23176 p hg
    simpa only [d2738, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2738, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23054 p hg
    simpa only [d2738, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23202 (p : Pattern) (guard : d5503 p = 1) : d2739 p ≤ (0 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2739, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23200 p hg
    simpa only [d2739, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2739, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23201 p hg
    simpa only [d2739, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23203 (p : Pattern) (guard : d5503 p = 1) : d2740 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2740, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23176 p hg
    simpa only [d2740, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2740, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23056 p hg
    simpa only [d2740, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23204 (p : Pattern) (guard : d5503 p = 1) : d2741 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2741, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23203 p hg
    simpa only [d2741, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2741, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2741, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23205 (p : Pattern) (guard : d5503 p = 1) : d2742 p ≤ (0 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2742, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23202 p hg
    simpa only [d2742, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2742, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23204 p hg
    simpa only [d2742, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23206 (p : Pattern) (guard : d5503 p = 1) : d2743 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2743, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23198 p hg
    simpa only [d2743, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2743, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23205 p hg
    simpa only [d2743, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23207 (p : Pattern) (guard : d5503 p = 1) : d2744 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2744, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23182 p hg
    simpa only [d2744, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2744, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23206 p hg
    simpa only [d2744, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23208 (p : Pattern) (guard : d5503 p = 1) : d2745 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2745, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23142 p hg
    simpa only [d2745, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2745, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2745, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23209 (p : Pattern) (guard : d5503 p = 1) : d2746 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2746, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23149 p hg
    simpa only [d2746, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2746, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23208 p hg
    simpa only [d2746, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23210 (p : Pattern) (guard : d5503 p = 1) : d2747 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2747, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23155 p hg
    simpa only [d2747, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2747, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2747, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23211 (p : Pattern) (guard : d5503 p = 1) : d2748 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2748, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23156 p hg
    simpa only [d2748, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2748, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23210 p hg
    simpa only [d2748, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23212 (p : Pattern) (guard : d5503 p = 1) : d2749 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2749, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23209 p hg
    simpa only [d2749, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2749, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23211 p hg
    simpa only [d2749, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23213 (p : Pattern) (guard : d5503 p = 1) : d2750 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2750, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23209 p hg
    simpa only [d2750, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2750, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23212 p hg
    simpa only [d2750, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23214 (p : Pattern) (guard : d5503 p = 1) : d2751 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2751, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23212 p hg
    simpa only [d2751, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2751, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23163 p hg
    simpa only [d2751, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23215 (p : Pattern) (guard : d5503 p = 1) : d2752 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2752, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23213 p hg
    simpa only [d2752, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2752, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23214 p hg
    simpa only [d2752, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23216 (p : Pattern) (guard : d5503 p = 1) : d2753 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2753, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23188 p hg
    simpa only [d2753, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2753, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23168 p hg
    simpa only [d2753, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23217 (p : Pattern) (guard : d0 p = 1) : d2707 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23218 (p : Pattern) (guard : d5503 p = 1) : d2707 p ≤ (0 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21426 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23217 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23219 (p : Pattern) (guard : d5503 p = 1) : d2754 p ≤ (0 : Int) + d120 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23218 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23171 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23220 (p : Pattern) (guard : d5503 p = 1) : d2755 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2755, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23219 p hg
    simpa only [d2755, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2755, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23172 p hg
    simpa only [d2755, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23221 (p : Pattern) (guard : d5503 p = 1) : d2756 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2756, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23216 p hg
    simpa only [d2756, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2756, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23220 p hg
    simpa only [d2756, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23222 (p : Pattern) (guard : d5503 p = 1) : d2757 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2757, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23221 p hg
    simpa only [d2757, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2757, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2757, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23223 (p : Pattern) (guard : d5503 p = 1) : d2758 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2758, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23222 p hg
    simpa only [d2758, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2758, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2758, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23224 (p : Pattern) (guard : d5503 p = 1) : d2759 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2759, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23215 p hg
    simpa only [d2759, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2759, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23223 p hg
    simpa only [d2759, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23225 (p : Pattern) (guard : d5503 p = 1) : d2760 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2760, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23209 p hg
    simpa only [d2760, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2760, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23216 p hg
    simpa only [d2760, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23226 (p : Pattern) (guard : d5503 p = 1) : d2761 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2761, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23211 p hg
    simpa only [d2761, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2761, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23041 p hg
    simpa only [d2761, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23227 (p : Pattern) (guard : d5503 p = 1) : d2762 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2762, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23225 p hg
    simpa only [d2762, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2762, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23226 p hg
    simpa only [d2762, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23228 (p : Pattern) (guard : d5503 p = 1) : d2763 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2763, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23211 p hg
    simpa only [d2763, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2763, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23046 p hg
    simpa only [d2763, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23229 (p : Pattern) (guard : d5503 p = 1) : d2764 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2764, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23228 p hg
    simpa only [d2764, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2764, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2764, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23230 (p : Pattern) (guard : d5503 p = 1) : d2765 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2765, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23227 p hg
    simpa only [d2765, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2765, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23229 p hg
    simpa only [d2765, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23231 (p : Pattern) (guard : d5503 p = 1) : d2766 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2766, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23220 p hg
    simpa only [d2766, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2766, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2766, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23232 (p : Pattern) (guard : d5503 p = 1) : d2767 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2767, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23231 p hg
    simpa only [d2767, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2767, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2767, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23233 (p : Pattern) (guard : d5503 p = 1) : d2768 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2768, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23232 p hg
    simpa only [d2768, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2768, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2768, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23234 (p : Pattern) (guard : d5503 p = 1) : d2769 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2769, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23230 p hg
    simpa only [d2769, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2769, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23233 p hg
    simpa only [d2769, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23235 (p : Pattern) (guard : d5503 p = 1) : d2770 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2770, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23224 p hg
    simpa only [d2770, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2770, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23234 p hg
    simpa only [d2770, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23236 (p : Pattern) (guard : d5503 p = 1) : d2771 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2771, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23207 p hg
    simpa only [d2771, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2771, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23235 p hg
    simpa only [d2771, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23237 (p : Pattern) (guard : d5503 p = 1) : d2772 p ≤ (0 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2772, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23163 p hg
    simpa only [d2772, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2772, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2772, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23238 (p : Pattern) (guard : d5503 p = 1) : d2773 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2773, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23237 p hg
    simpa only [d2773, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2773, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2773, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23239 (p : Pattern) (guard : d5503 p = 1) : d2774 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2774, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23238 p hg
    simpa only [d2774, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2774, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2774, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
