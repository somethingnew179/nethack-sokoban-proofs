/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons325
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45640 (p : Pattern) (guard : d8124 p = 1) : d3308 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45637 p hg
    simpa only [d8124, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45639 p hg
    simpa only [d8124, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45641 (p : Pattern) (guard : d0 p = 1) : d3260 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45642 (p : Pattern) (guard : d8117 p = 1) : d3451 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45610 p hg
    simpa only [d8117, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45641 p hg
    simpa only [d8117, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45643 (p : Pattern) (guard : d0 p = 1) : d3452 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45644 (p : Pattern) (guard : d8123 p = 1) : d3453 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45642 p hg
    simpa only [d8123, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45643 p hg
    simpa only [d8123, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45645 (p : Pattern) (guard : d0 p = 1) : d3455 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45646 (p : Pattern) (guard : d8129 p = 1) : d3456 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45644 p hg
    simpa only [d8129, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45645 p hg
    simpa only [d8129, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45647 (p : Pattern) (guard : d8130 p = 1) : d3457 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3457, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45640 p hg
    simpa only [d8130, d3457, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3457, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45646 p hg
    simpa only [d8130, d3457, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45648 (p : Pattern) (guard : d8131 p = 1) : d3458 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3458, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45619 p hg
    simpa only [d8131, d3458, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3458, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45647 p hg
    simpa only [d8131, d3458, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45649 (p : Pattern) (guard : d8105 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45650 (p : Pattern) (guard : d0 p = 1) : d3230 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45651 (p : Pattern) (guard : d8111 p = 1) : d3238 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45649 p hg
    simpa only [d8111, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45650 p hg
    simpa only [d8111, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45652 (p : Pattern) (guard : d8112 p = 1) : d3238 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45147 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45651 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45653 (p : Pattern) (guard : d0 p = 1) : d3301 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45654 (p : Pattern) (guard : d8117 p = 1) : d3302 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44990 p hg
    simpa only [d8117, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45653 p hg
    simpa only [d8117, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45655 (p : Pattern) (guard : d8118 p = 1) : d3459 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3459, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45652 p hg
    simpa only [d8118, d3459, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3459, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45654 p hg
    simpa only [d8118, d3459, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45656 (p : Pattern) (guard : d8123 p = 1) : d3303 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45654 p hg
    simpa only [d8123, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44997 p hg
    simpa only [d8123, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45657 (p : Pattern) (guard : d8124 p = 1) : d3460 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3460, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45655 p hg
    simpa only [d8124, d3460, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3460, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45656 p hg
    simpa only [d8124, d3460, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45658 (p : Pattern) (guard : d0 p = 1) : d3463 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45659 (p : Pattern) (guard : d8117 p = 1) : d3464 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44971 p hg
    simpa only [d8117, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45658 p hg
    simpa only [d8117, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45660 (p : Pattern) (guard : d8123 p = 1) : d3465 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45659 p hg
    simpa only [d8123, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45661 (p : Pattern) (guard : d8129 p = 1) : d3466 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45660 p hg
    simpa only [d8129, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45662 (p : Pattern) (guard : d8130 p = 1) : d3467 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3467, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45657 p hg
    simpa only [d8130, d3467, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3467, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45661 p hg
    simpa only [d8130, d3467, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45663 (p : Pattern) (guard : d0 p = 1) : d3275 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45664 (p : Pattern) (guard : d8117 p = 1) : d3275 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45558 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45663 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45665 (p : Pattern) (guard : d0 p = 1) : d3468 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45666 (p : Pattern) (guard : d8123 p = 1) : d3469 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3469, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45664 p hg
    simpa only [d8123, d3469, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3469, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45665 p hg
    simpa only [d8123, d3469, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45667 (p : Pattern) (guard : d0 p = 1) : d3310 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45668 (p : Pattern) (guard : d8129 p = 1) : d3470 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3470, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45666 p hg
    simpa only [d8129, d3470, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3470, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45667 p hg
    simpa only [d8129, d3470, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45669 (p : Pattern) (guard : d0 p = 1) : d3473 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45670 (p : Pattern) (guard : d8135 p = 1) : d3474 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3474, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45668 p hg
    simpa only [d8135, d3474, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3474, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45669 p hg
    simpa only [d8135, d3474, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45671 (p : Pattern) (guard : d8136 p = 1) : d3475 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3475, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45662 p hg
    simpa only [d8136, d3475, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3475, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45670 p hg
    simpa only [d8136, d3475, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45672 (p : Pattern) (guard : d8137 p = 1) : d3476 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3476, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45648 p hg
    simpa only [d8137, d3476, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3476, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45671 p hg
    simpa only [d8137, d3476, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45673 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34145 p hg
    simpa only [d5847, d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45674 (p : Pattern) (guard : d5854 p = 1) : d3226 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45673 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45675 (p : Pattern) (guard : d8099 p = 1) : d3226 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45674 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45676 (p : Pattern) (guard : d8105 p = 1) : d3226 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45675 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45677 (p : Pattern) (guard : d8111 p = 1) : d3238 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45676 p hg
    simpa only [d8111, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45650 p hg
    simpa only [d8111, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45678 (p : Pattern) (guard : d8112 p = 1) : d3238 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45553 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45677 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45679 (p : Pattern) (guard : d8118 p = 1) : d3459 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3459, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45678 p hg
    simpa only [d8118, d3459, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3459, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45654 p hg
    simpa only [d8118, d3459, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45680 (p : Pattern) (guard : d8124 p = 1) : d3460 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3460, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45679 p hg
    simpa only [d8124, d3460, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3460, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45656 p hg
    simpa only [d8124, d3460, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45681 (p : Pattern) (guard : d8130 p = 1) : d3467 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3467, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45680 p hg
    simpa only [d8130, d3467, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3467, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45661 p hg
    simpa only [d8130, d3467, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45682 (p : Pattern) (guard : d8117 p = 1) : d3275 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45583 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45663 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45683 (p : Pattern) (guard : d8123 p = 1) : d3469 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3469, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45682 p hg
    simpa only [d8123, d3469, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3469, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45665 p hg
    simpa only [d8123, d3469, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45684 (p : Pattern) (guard : d8129 p = 1) : d3470 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3470, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45683 p hg
    simpa only [d8129, d3470, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3470, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45667 p hg
    simpa only [d8129, d3470, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45685 (p : Pattern) (guard : d8135 p = 1) : d3474 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3474, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45684 p hg
    simpa only [d8135, d3474, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3474, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45669 p hg
    simpa only [d8135, d3474, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45686 (p : Pattern) (guard : d8136 p = 1) : d3475 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3475, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45681 p hg
    simpa only [d8136, d3475, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3475, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45685 p hg
    simpa only [d8136, d3475, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45687 (p : Pattern) (guard : d8142 p = 1) : d3477 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3477, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45686 p hg
    simpa only [d8142, d3477, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3477, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d3477, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45688 (p : Pattern) (guard : d8143 p = 1) : d3478 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3478, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45672 p hg
    simpa only [d8143, d3478, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3478, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45687 p hg
    simpa only [d8143, d3478, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45689 (p : Pattern) (guard : d8144 p = 1) : d3479 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d3479, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45604 p hg
    simpa only [d8144, d3479, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d3479, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45688 p hg
    simpa only [d8144, d3479, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45690 (p : Pattern) (guard : d8145 p = 1) : d3480 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d3480, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45155 p hg
    simpa only [d8145, d3480, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d3480, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45689 p hg
    simpa only [d8145, d3480, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45691 (p : Pattern) (guard : d8086 p = 1) : d3228 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3228, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44342 p hg
    simpa only [d8086, d3228, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3228, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44883 p hg
    simpa only [d8086, d3228, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45692 (p : Pattern) (guard : d8091 p = 1) : d3229 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45691 p hg
    simpa only [d8091, d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44859 p hg
    simpa only [d8091, d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45693 (p : Pattern) (guard : d8095 p = 1) : d3230 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44884 p hg
    simpa only [d8095, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45694 (p : Pattern) (guard : d8096 p = 1) : d3231 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45692 p hg
    simpa only [d8096, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45693 p hg
    simpa only [d8096, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45695 (p : Pattern) (guard : d8102 p = 1) : d3237 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45694 p hg
    simpa only [d8102, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45510 p hg
    simpa only [d8102, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45696 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45485 p hg
    simpa only [d8107, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45521 p hg
    simpa only [d8107, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45697 (p : Pattern) (guard : d8108 p = 1) : d3243 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45695 p hg
    simpa only [d8108, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45696 p hg
    simpa only [d8108, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45698 (p : Pattern) (guard : d8112 p = 1) : d3247 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45060 p hg
    simpa only [d8112, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45699 (p : Pattern) (guard : d8113 p = 1) : d3248 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45492 p hg
    simpa only [d8113, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45698 p hg
    simpa only [d8113, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45700 (p : Pattern) (guard : d8114 p = 1) : d3249 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45697 p hg
    simpa only [d8114, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45699 p hg
    simpa only [d8114, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45701 (p : Pattern) (guard : d8101 p = 1) : d3252 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44936 p hg
    simpa only [d8101, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45702 (p : Pattern) (guard : d8107 p = 1) : d3256 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45701 p hg
    simpa only [d8107, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45537 p hg
    simpa only [d8107, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45703 (p : Pattern) (guard : d8106 p = 1) : d3259 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45013 p hg
    simpa only [d8106, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44599 p hg
    simpa only [d8106, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45704 (p : Pattern) (guard : d8112 p = 1) : d3261 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45703 p hg
    simpa only [d8112, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d8112, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45705 (p : Pattern) (guard : d8113 p = 1) : d3262 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45702 p hg
    simpa only [d8113, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45704 p hg
    simpa only [d8113, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45706 (p : Pattern) (guard : d8106 p = 1) : d3263 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44987 p hg
    simpa only [d8106, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45707 (p : Pattern) (guard : d8112 p = 1) : d3264 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45706 p hg
    simpa only [d8112, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d8112, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45708 (p : Pattern) (guard : d8118 p = 1) : d3267 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45707 p hg
    simpa only [d8118, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44930 p hg
    simpa only [d8118, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45709 (p : Pattern) (guard : d8119 p = 1) : d3268 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45705 p hg
    simpa only [d8119, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45708 p hg
    simpa only [d8119, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45710 (p : Pattern) (guard : d8120 p = 1) : d3269 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45700 p hg
    simpa only [d8120, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45709 p hg
    simpa only [d8120, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45711 (p : Pattern) (guard : d8085 p = 1) : d3271 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3271, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44468 p hg
    simpa only [d8085, d3271, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3271, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45010 p hg
    simpa only [d8085, d3271, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45712 (p : Pattern) (guard : d8090 p = 1) : d3272 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45711 p hg
    simpa only [d8090, d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45144 p hg
    simpa only [d8090, d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45713 (p : Pattern) (guard : d8095 p = 1) : d3273 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45712 p hg
    simpa only [d8095, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45012 p hg
    simpa only [d8095, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45714 (p : Pattern) (guard : d8100 p = 1) : d3230 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45145 p hg
    simpa only [d8100, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45715 (p : Pattern) (guard : d8101 p = 1) : d3274 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45713 p hg
    simpa only [d8101, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45714 p hg
    simpa only [d8101, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45716 (p : Pattern) (guard : d8084 p = 1) : d3250 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3250, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34467 p hg
    simpa only [d8084, d3250, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3250, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3250, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45717 (p : Pattern) (guard : d8089 p = 1) : d3250 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45716 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45718 (p : Pattern) (guard : d8094 p = 1) : d3250 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45717 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45719 (p : Pattern) (guard : d8100 p = 1) : d3250 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45718 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45720 (p : Pattern) (guard : d8106 p = 1) : d3275 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45719 p hg
    simpa only [d8106, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d8106, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45721 (p : Pattern) (guard : d8107 p = 1) : d3276 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45715 p hg
    simpa only [d8107, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45720 p hg
    simpa only [d8107, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45722 (p : Pattern) (guard : d8084 p = 1) : d3239 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3239, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34479 p hg
    simpa only [d8084, d3239, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3239, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3239, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45723 (p : Pattern) (guard : d8089 p = 1) : d3239 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45722 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45724 (p : Pattern) (guard : d8094 p = 1) : d3239 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45723 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45725 (p : Pattern) (guard : d8100 p = 1) : d3239 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45724 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45726 (p : Pattern) (guard : d8106 p = 1) : d3241 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45725 p hg
    simpa only [d8106, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44724 p hg
    simpa only [d8106, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45727 (p : Pattern) (guard : d8099 p = 1) : d3244 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28772 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45728 (p : Pattern) (guard : d8105 p = 1) : d3244 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45727 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45729 (p : Pattern) (guard : d8111 p = 1) : d3246 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45728 p hg
    simpa only [d8111, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44748 p hg
    simpa only [d8111, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45730 (p : Pattern) (guard : d8112 p = 1) : d3277 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45726 p hg
    simpa only [d8112, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45729 p hg
    simpa only [d8112, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45731 (p : Pattern) (guard : d8113 p = 1) : d3278 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45721 p hg
    simpa only [d8113, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45730 p hg
    simpa only [d8113, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45732 (p : Pattern) (guard : d8112 p = 1) : d3282 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45521 p hg
    simpa only [d8112, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45270 p hg
    simpa only [d8112, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45733 (p : Pattern) (guard : d8117 p = 1) : d3284 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45275 p hg
    simpa only [d8117, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45734 (p : Pattern) (guard : d8118 p = 1) : d3285 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45732 p hg
    simpa only [d8118, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45733 p hg
    simpa only [d8118, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45735 (p : Pattern) (guard : d8119 p = 1) : d3286 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45731 p hg
    simpa only [d8119, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45734 p hg
    simpa only [d8119, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45736 (p : Pattern) (guard : d8106 p = 1) : d3255 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45552 p hg
    simpa only [d8106, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44735 p hg
    simpa only [d8106, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45737 (p : Pattern) (guard : d8111 p = 1) : d3287 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45557 p hg
    simpa only [d8111, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45738 (p : Pattern) (guard : d8112 p = 1) : d3288 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45736 p hg
    simpa only [d8112, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45737 p hg
    simpa only [d8112, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45739 (p : Pattern) (guard : d8118 p = 1) : d3290 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45738 p hg
    simpa only [d8118, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44958 p hg
    simpa only [d8118, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45740 (p : Pattern) (guard : d8124 p = 1) : d3296 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45739 p hg
    simpa only [d8124, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44963 p hg
    simpa only [d8124, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45741 (p : Pattern) (guard : d8125 p = 1) : d3297 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45735 p hg
    simpa only [d8125, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45740 p hg
    simpa only [d8125, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45742 (p : Pattern) (guard : d8126 p = 1) : d3298 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45710 p hg
    simpa only [d8126, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45741 p hg
    simpa only [d8126, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45743 (p : Pattern) (guard : d8132 p = 1) : d3314 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45742 p hg
    simpa only [d8132, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45594 p hg
    simpa only [d8132, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45744 (p : Pattern) (guard : d8112 p = 1) : d3302 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44891 p hg
    simpa only [d8112, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44979 p hg
    simpa only [d8112, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45745 (p : Pattern) (guard : d8118 p = 1) : d3303 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45744 p hg
    simpa only [d8118, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45746 (p : Pattern) (guard : d8124 p = 1) : d3304 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45745 p hg
    simpa only [d8124, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45747 (p : Pattern) (guard : d8125 p = 1) : d3305 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45609 p hg
    simpa only [d8125, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45746 p hg
    simpa only [d8125, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45748 (p : Pattern) (guard : d8130 p = 1) : d3312 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45640 p hg
    simpa only [d8130, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45002 p hg
    simpa only [d8130, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45749 (p : Pattern) (guard : d8131 p = 1) : d3313 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45747 p hg
    simpa only [d8131, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45748 p hg
    simpa only [d8131, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45750 (p : Pattern) (guard : d8112 p = 1) : d3315 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45060 p hg
    simpa only [d8112, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44756 p hg
    simpa only [d8112, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45751 (p : Pattern) (guard : d8118 p = 1) : d3316 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45750 p hg
    simpa only [d8118, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45752 (p : Pattern) (guard : d8124 p = 1) : d3318 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45751 p hg
    simpa only [d8124, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45597 p hg
    simpa only [d8124, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45753 (p : Pattern) (guard : d8130 p = 1) : d3320 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45752 p hg
    simpa only [d8130, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45599 p hg
    simpa only [d8130, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45754 (p : Pattern) (guard : d8123 p = 1) : d3317 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45733 p hg
    simpa only [d8123, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45755 (p : Pattern) (guard : d8129 p = 1) : d3319 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45754 p hg
    simpa only [d8129, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45756 (p : Pattern) (guard : d8135 p = 1) : d3321 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45755 p hg
    simpa only [d8135, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45757 (p : Pattern) (guard : d8136 p = 1) : d3322 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45753 p hg
    simpa only [d8136, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45756 p hg
    simpa only [d8136, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45758 (p : Pattern) (guard : d8137 p = 1) : d3323 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45749 p hg
    simpa only [d8137, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45757 p hg
    simpa only [d8137, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45759 (p : Pattern) (guard : d8138 p = 1) : d3324 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45743 p hg
    simpa only [d8138, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45758 p hg
    simpa only [d8138, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45760 (p : Pattern) (guard : d8107 p = 1) : d3325 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45510 p hg
    simpa only [d8107, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45624 p hg
    simpa only [d8107, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45761 (p : Pattern) (guard : d8112 p = 1) : d3242 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45578 p hg
    simpa only [d8112, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45635 p hg
    simpa only [d8112, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45762 (p : Pattern) (guard : d8113 p = 1) : d3326 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45760 p hg
    simpa only [d8113, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45761 p hg
    simpa only [d8113, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45763 (p : Pattern) (guard : d8118 p = 1) : d3248 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45606 p hg
    simpa only [d8118, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44974 p hg
    simpa only [d8118, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45764 (p : Pattern) (guard : d8119 p = 1) : d3327 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45762 p hg
    simpa only [d8119, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45763 p hg
    simpa only [d8119, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45765 (p : Pattern) (guard : d8106 p = 1) : d3252 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45146 p hg
    simpa only [d8106, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d8106, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45766 (p : Pattern) (guard : d8111 p = 1) : d3255 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45649 p hg
    simpa only [d8111, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44978 p hg
    simpa only [d8111, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45767 (p : Pattern) (guard : d8112 p = 1) : d3256 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45765 p hg
    simpa only [d8112, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45766 p hg
    simpa only [d8112, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45768 (p : Pattern) (guard : d8111 p = 1) : d3259 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45649 p hg
    simpa only [d8111, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44755 p hg
    simpa only [d8111, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45769 (p : Pattern) (guard : d8117 p = 1) : d3261 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45768 p hg
    simpa only [d8117, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45641 p hg
    simpa only [d8117, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45770 (p : Pattern) (guard : d8118 p = 1) : d3262 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45767 p hg
    simpa only [d8118, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45769 p hg
    simpa only [d8118, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45771 (p : Pattern) (guard : d8111 p = 1) : d3263 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45649 p hg
    simpa only [d8111, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45772 (p : Pattern) (guard : d8117 p = 1) : d3264 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45771 p hg
    simpa only [d8117, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45641 p hg
    simpa only [d8117, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45773 (p : Pattern) (guard : d0 p = 1) : d3266 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45774 (p : Pattern) (guard : d8123 p = 1) : d3267 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45772 p hg
    simpa only [d8123, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45773 p hg
    simpa only [d8123, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45775 (p : Pattern) (guard : d8124 p = 1) : d3268 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45770 p hg
    simpa only [d8124, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45774 p hg
    simpa only [d8124, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45776 (p : Pattern) (guard : d8125 p = 1) : d3328 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45764 p hg
    simpa only [d8125, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45775 p hg
    simpa only [d8125, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45777 (p : Pattern) (guard : d8084 p = 1) : d3226 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3226, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33842 p hg
    simpa only [d8084, d3226, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3226, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3226, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45778 (p : Pattern) (guard : d8089 p = 1) : d3226 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45777 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45779 (p : Pattern) (guard : d8094 p = 1) : d3226 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45778 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
