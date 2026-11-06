/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons307
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43120 (p : Pattern) (guard : d8089 p = 1) : d2504 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35509 p hg
    simpa only [d8089, d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43121 (p : Pattern) (guard : d8094 p = 1) : d2504 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43120 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43122 (p : Pattern) (guard : d8100 p = 1) : d2518 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43121 p hg
    simpa only [d8100, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8100, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43123 (p : Pattern) (guard : d8106 p = 1) : d2601 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43122 p hg
    simpa only [d8106, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42450 p hg
    simpa only [d8106, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43124 (p : Pattern) (guard : d5854 p = 1) : d2540 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35515 p hg
    simpa only [d5854, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43125 (p : Pattern) (guard : d8099 p = 1) : d2540 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43124 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21708 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43126 (p : Pattern) (guard : d8105 p = 1) : d2569 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43125 p hg
    simpa only [d8105, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22597 p hg
    simpa only [d8105, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43127 (p : Pattern) (guard : d8111 p = 1) : d2611 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43126 p hg
    simpa only [d8111, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42472 p hg
    simpa only [d8111, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43128 (p : Pattern) (guard : d8112 p = 1) : d2618 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43123 p hg
    simpa only [d8112, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43127 p hg
    simpa only [d8112, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43129 (p : Pattern) (guard : d5854 p = 1) : d2520 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35522 p hg
    simpa only [d5854, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43130 (p : Pattern) (guard : d8099 p = 1) : d2520 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43129 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21653 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43131 (p : Pattern) (guard : d8105 p = 1) : d2523 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43130 p hg
    simpa only [d8105, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22564 p hg
    simpa only [d8105, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43132 (p : Pattern) (guard : d8111 p = 1) : d2603 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43131 p hg
    simpa only [d8111, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42453 p hg
    simpa only [d8111, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43133 (p : Pattern) (guard : d8117 p = 1) : d2619 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43132 p hg
    simpa only [d8117, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42475 p hg
    simpa only [d8117, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43134 (p : Pattern) (guard : d8118 p = 1) : d2620 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43128 p hg
    simpa only [d8118, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43133 p hg
    simpa only [d8118, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43135 (p : Pattern) (guard : d8117 p = 1) : d2621 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43086 p hg
    simpa only [d8117, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d8117, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43136 (p : Pattern) (guard : d8123 p = 1) : d2622 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43135 p hg
    simpa only [d8123, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42480 p hg
    simpa only [d8123, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43137 (p : Pattern) (guard : d8124 p = 1) : d2623 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43134 p hg
    simpa only [d8124, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43136 p hg
    simpa only [d8124, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43138 (p : Pattern) (guard : d0 p = 1) : d2555 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43139 (p : Pattern) (guard : d8117 p = 1) : d2802 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43110 p hg
    simpa only [d8117, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43138 p hg
    simpa only [d8117, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43140 (p : Pattern) (guard : d0 p = 1) : d2803 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43141 (p : Pattern) (guard : d8123 p = 1) : d2804 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43139 p hg
    simpa only [d8123, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43140 p hg
    simpa only [d8123, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43142 (p : Pattern) (guard : d0 p = 1) : d2806 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43143 (p : Pattern) (guard : d8129 p = 1) : d2807 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43141 p hg
    simpa only [d8129, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43142 p hg
    simpa only [d8129, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43144 (p : Pattern) (guard : d8130 p = 1) : d2808 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2808, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43137 p hg
    simpa only [d8130, d2808, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2808, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43143 p hg
    simpa only [d8130, d2808, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43145 (p : Pattern) (guard : d8131 p = 1) : d2809 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2809, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43119 p hg
    simpa only [d8131, d2809, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2809, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43144 p hg
    simpa only [d8131, d2809, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43146 (p : Pattern) (guard : d8099 p = 1) : d2504 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21664 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43147 (p : Pattern) (guard : d8105 p = 1) : d2518 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43146 p hg
    simpa only [d8105, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22561 p hg
    simpa only [d8105, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43148 (p : Pattern) (guard : d0 p = 1) : d2600 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43149 (p : Pattern) (guard : d8111 p = 1) : d2601 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43147 p hg
    simpa only [d8111, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43148 p hg
    simpa only [d8111, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43150 (p : Pattern) (guard : d8112 p = 1) : d2601 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42644 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43149 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43151 (p : Pattern) (guard : d0 p = 1) : d2613 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43152 (p : Pattern) (guard : d8117 p = 1) : d2614 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42473 p hg
    simpa only [d8117, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43151 p hg
    simpa only [d8117, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43153 (p : Pattern) (guard : d8118 p = 1) : d2810 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2810, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43150 p hg
    simpa only [d8118, d2810, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2810, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43152 p hg
    simpa only [d8118, d2810, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43154 (p : Pattern) (guard : d8123 p = 1) : d2615 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43152 p hg
    simpa only [d8123, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42480 p hg
    simpa only [d8123, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43155 (p : Pattern) (guard : d8124 p = 1) : d2811 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2811, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43153 p hg
    simpa only [d8124, d2811, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2811, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43154 p hg
    simpa only [d8124, d2811, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43156 (p : Pattern) (guard : d0 p = 1) : d2816 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43157 (p : Pattern) (guard : d8117 p = 1) : d2817 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42454 p hg
    simpa only [d8117, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43156 p hg
    simpa only [d8117, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43158 (p : Pattern) (guard : d8123 p = 1) : d2818 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43157 p hg
    simpa only [d8123, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43159 (p : Pattern) (guard : d8129 p = 1) : d2819 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43158 p hg
    simpa only [d8129, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43160 (p : Pattern) (guard : d8130 p = 1) : d2820 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2820, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43155 p hg
    simpa only [d8130, d2820, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2820, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43159 p hg
    simpa only [d8130, d2820, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43161 (p : Pattern) (guard : d0 p = 1) : d2611 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43162 (p : Pattern) (guard : d8117 p = 1) : d2611 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43057 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43161 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43163 (p : Pattern) (guard : d0 p = 1) : d2821 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43164 (p : Pattern) (guard : d8123 p = 1) : d2822 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2822, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43162 p hg
    simpa only [d8123, d2822, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2822, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43163 p hg
    simpa only [d8123, d2822, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43165 (p : Pattern) (guard : d0 p = 1) : d2625 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43166 (p : Pattern) (guard : d8129 p = 1) : d2823 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2823, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43164 p hg
    simpa only [d8129, d2823, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2823, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43165 p hg
    simpa only [d8129, d2823, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43167 (p : Pattern) (guard : d0 p = 1) : d2826 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43168 (p : Pattern) (guard : d8135 p = 1) : d2827 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2827, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43166 p hg
    simpa only [d8135, d2827, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2827, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43167 p hg
    simpa only [d8135, d2827, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43169 (p : Pattern) (guard : d8136 p = 1) : d2828 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2828, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43160 p hg
    simpa only [d8136, d2828, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2828, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43168 p hg
    simpa only [d8136, d2828, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43170 (p : Pattern) (guard : d8137 p = 1) : d2829 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2829, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43145 p hg
    simpa only [d8137, d2829, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2829, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43169 p hg
    simpa only [d8137, d2829, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43171 (p : Pattern) (guard : d5854 p = 1) : d2504 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35549 p hg
    simpa only [d5854, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43172 (p : Pattern) (guard : d8099 p = 1) : d2504 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43171 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21664 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43173 (p : Pattern) (guard : d8105 p = 1) : d2518 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43172 p hg
    simpa only [d8105, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22561 p hg
    simpa only [d8105, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43174 (p : Pattern) (guard : d8111 p = 1) : d2601 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43173 p hg
    simpa only [d8111, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43148 p hg
    simpa only [d8111, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43175 (p : Pattern) (guard : d8112 p = 1) : d2601 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43053 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43174 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43176 (p : Pattern) (guard : d8118 p = 1) : d2810 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2810, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43175 p hg
    simpa only [d8118, d2810, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2810, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43152 p hg
    simpa only [d8118, d2810, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43177 (p : Pattern) (guard : d8124 p = 1) : d2811 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2811, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43176 p hg
    simpa only [d8124, d2811, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2811, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43154 p hg
    simpa only [d8124, d2811, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43178 (p : Pattern) (guard : d8130 p = 1) : d2820 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2820, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43177 p hg
    simpa only [d8130, d2820, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2820, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43159 p hg
    simpa only [d8130, d2820, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43179 (p : Pattern) (guard : d8117 p = 1) : d2611 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43081 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43161 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43180 (p : Pattern) (guard : d8123 p = 1) : d2822 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2822, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43179 p hg
    simpa only [d8123, d2822, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2822, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43163 p hg
    simpa only [d8123, d2822, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43181 (p : Pattern) (guard : d8129 p = 1) : d2823 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2823, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43180 p hg
    simpa only [d8129, d2823, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2823, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43165 p hg
    simpa only [d8129, d2823, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43182 (p : Pattern) (guard : d8135 p = 1) : d2827 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2827, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43181 p hg
    simpa only [d8135, d2827, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2827, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43167 p hg
    simpa only [d8135, d2827, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43183 (p : Pattern) (guard : d8136 p = 1) : d2828 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2828, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43178 p hg
    simpa only [d8136, d2828, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2828, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43182 p hg
    simpa only [d8136, d2828, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43184 (p : Pattern) (guard : d8142 p = 1) : d2830 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2830, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43183 p hg
    simpa only [d8142, d2830, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2830, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2830, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43185 (p : Pattern) (guard : d8143 p = 1) : d2831 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2831, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43170 p hg
    simpa only [d8143, d2831, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2831, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43184 p hg
    simpa only [d8143, d2831, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43186 (p : Pattern) (guard : d8144 p = 1) : d2832 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2832, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43102 p hg
    simpa only [d8144, d2832, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2832, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43185 p hg
    simpa only [d8144, d2832, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43187 (p : Pattern) (guard : d8145 p = 1) : d2833 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d2833, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42652 p hg
    simpa only [d8145, d2833, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d2833, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43186 p hg
    simpa only [d8145, d2833, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43188 (p : Pattern) (guard : d8086 p = 1) : d2505 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2505, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41772 p hg
    simpa only [d8086, d2505, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2505, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42349 p hg
    simpa only [d8086, d2505, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43189 (p : Pattern) (guard : d8090 p = 1) : d2507 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d8090, d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41853 p hg
    simpa only [d8090, d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43190 (p : Pattern) (guard : d8091 p = 1) : d2508 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43188 p hg
    simpa only [d8091, d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43189 p hg
    simpa only [d8091, d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43191 (p : Pattern) (guard : d8090 p = 1) : d2510 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42349 p hg
    simpa only [d8090, d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42092 p hg
    simpa only [d8090, d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43192 (p : Pattern) (guard : d8095 p = 1) : d2511 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43191 p hg
    simpa only [d8095, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43193 (p : Pattern) (guard : d8096 p = 1) : d2512 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43190 p hg
    simpa only [d8096, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43192 p hg
    simpa only [d8096, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43194 (p : Pattern) (guard : d8102 p = 1) : d2517 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43193 p hg
    simpa only [d8102, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43015 p hg
    simpa only [d8102, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43195 (p : Pattern) (guard : d8107 p = 1) : d2528 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d8107, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43024 p hg
    simpa only [d8107, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43196 (p : Pattern) (guard : d8108 p = 1) : d2529 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43194 p hg
    simpa only [d8108, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43195 p hg
    simpa only [d8108, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43197 (p : Pattern) (guard : d8112 p = 1) : d2537 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42545 p hg
    simpa only [d8112, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43198 (p : Pattern) (guard : d8113 p = 1) : d2538 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42995 p hg
    simpa only [d8113, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43197 p hg
    simpa only [d8113, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43199 (p : Pattern) (guard : d8114 p = 1) : d2539 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43196 p hg
    simpa only [d8114, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43198 p hg
    simpa only [d8114, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43200 (p : Pattern) (guard : d8101 p = 1) : d2544 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42416 p hg
    simpa only [d8101, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d8101, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43201 (p : Pattern) (guard : d8107 p = 1) : d2550 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43200 p hg
    simpa only [d8107, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43038 p hg
    simpa only [d8107, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43202 (p : Pattern) (guard : d8106 p = 1) : d2554 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42495 p hg
    simpa only [d8106, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42033 p hg
    simpa only [d8106, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43203 (p : Pattern) (guard : d8112 p = 1) : d2556 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43202 p hg
    simpa only [d8112, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42405 p hg
    simpa only [d8112, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43204 (p : Pattern) (guard : d8113 p = 1) : d2557 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43201 p hg
    simpa only [d8113, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43203 p hg
    simpa only [d8113, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43205 (p : Pattern) (guard : d8106 p = 1) : d2558 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42470 p hg
    simpa only [d8106, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43206 (p : Pattern) (guard : d8112 p = 1) : d2559 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43205 p hg
    simpa only [d8112, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42405 p hg
    simpa only [d8112, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43207 (p : Pattern) (guard : d8118 p = 1) : d2562 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43206 p hg
    simpa only [d8118, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42410 p hg
    simpa only [d8118, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43208 (p : Pattern) (guard : d8119 p = 1) : d2563 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43204 p hg
    simpa only [d8119, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43207 p hg
    simpa only [d8119, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43209 (p : Pattern) (guard : d8120 p = 1) : d2564 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43199 p hg
    simpa only [d8120, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43208 p hg
    simpa only [d8120, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43210 (p : Pattern) (guard : d8084 p = 1) : d329 p ≤ (0 : Int) + d329 p := by
  omega
theorem compare43211 (p : Pattern) (guard : d8085 p = 1) : d2565 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2565, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34461 p hg
    simpa only [d8085, d2565, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2565, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43210 p hg
    simpa only [d8085, d2565, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43212 (p : Pattern) (guard : d8090 p = 1) : d2566 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43211 p hg
    simpa only [d8090, d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42641 p hg
    simpa only [d8090, d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43213 (p : Pattern) (guard : d8094 p = 1) : d2507 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42493 p hg
    simpa only [d8094, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42114 p hg
    simpa only [d8094, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43214 (p : Pattern) (guard : d8095 p = 1) : d2567 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43212 p hg
    simpa only [d8095, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43213 p hg
    simpa only [d8095, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43215 (p : Pattern) (guard : d8094 p = 1) : d2510 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42641 p hg
    simpa only [d8094, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42378 p hg
    simpa only [d8094, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43216 (p : Pattern) (guard : d8100 p = 1) : d2511 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43215 p hg
    simpa only [d8100, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43217 (p : Pattern) (guard : d8101 p = 1) : d2568 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43214 p hg
    simpa only [d8101, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43216 p hg
    simpa only [d8101, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43218 (p : Pattern) (guard : d8089 p = 1) : d2540 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35588 p hg
    simpa only [d8089, d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43219 (p : Pattern) (guard : d8094 p = 1) : d2540 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43218 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43220 (p : Pattern) (guard : d8100 p = 1) : d2569 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43219 p hg
    simpa only [d8100, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d8100, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43221 (p : Pattern) (guard : d8106 p = 1) : d2573 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43220 p hg
    simpa only [d8106, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42422 p hg
    simpa only [d8106, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43222 (p : Pattern) (guard : d8107 p = 1) : d2574 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43217 p hg
    simpa only [d8107, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43221 p hg
    simpa only [d8107, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43223 (p : Pattern) (guard : d8089 p = 1) : d2520 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35594 p hg
    simpa only [d8089, d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43224 (p : Pattern) (guard : d8094 p = 1) : d2520 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43223 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43225 (p : Pattern) (guard : d8100 p = 1) : d2523 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43224 p hg
    simpa only [d8100, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d8100, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43226 (p : Pattern) (guard : d8106 p = 1) : d2527 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43225 p hg
    simpa only [d8106, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42385 p hg
    simpa only [d8106, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43227 (p : Pattern) (guard : d5854 p = 1) : d2530 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19895 p hg
    simpa only [d5854, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43228 (p : Pattern) (guard : d8099 p = 1) : d2530 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43227 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21669 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43229 (p : Pattern) (guard : d8105 p = 1) : d2532 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43228 p hg
    simpa only [d8105, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22570 p hg
    simpa only [d8105, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43230 (p : Pattern) (guard : d8111 p = 1) : d2536 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43229 p hg
    simpa only [d8111, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42429 p hg
    simpa only [d8111, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43231 (p : Pattern) (guard : d8112 p = 1) : d2575 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43226 p hg
    simpa only [d8112, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43230 p hg
    simpa only [d8112, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43232 (p : Pattern) (guard : d8113 p = 1) : d2576 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43222 p hg
    simpa only [d8113, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43231 p hg
    simpa only [d8113, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43233 (p : Pattern) (guard : d8112 p = 1) : d2582 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43024 p hg
    simpa only [d8112, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42764 p hg
    simpa only [d8112, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43234 (p : Pattern) (guard : d8117 p = 1) : d2585 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42770 p hg
    simpa only [d8117, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43235 (p : Pattern) (guard : d8118 p = 1) : d2586 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43233 p hg
    simpa only [d8118, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43234 p hg
    simpa only [d8118, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43236 (p : Pattern) (guard : d8119 p = 1) : d2587 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43232 p hg
    simpa only [d8119, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43235 p hg
    simpa only [d8119, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43237 (p : Pattern) (guard : d8106 p = 1) : d2549 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43052 p hg
    simpa only [d8106, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42201 p hg
    simpa only [d8106, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43238 (p : Pattern) (guard : d8111 p = 1) : d2588 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43056 p hg
    simpa only [d8111, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43239 (p : Pattern) (guard : d8112 p = 1) : d2589 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43237 p hg
    simpa only [d8112, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43238 p hg
    simpa only [d8112, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43240 (p : Pattern) (guard : d8118 p = 1) : d2591 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43239 p hg
    simpa only [d8118, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42441 p hg
    simpa only [d8118, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43241 (p : Pattern) (guard : d8124 p = 1) : d2597 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43240 p hg
    simpa only [d8124, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42446 p hg
    simpa only [d8124, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43242 (p : Pattern) (guard : d8125 p = 1) : d2598 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43236 p hg
    simpa only [d8125, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43241 p hg
    simpa only [d8125, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43243 (p : Pattern) (guard : d8126 p = 1) : d2599 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43209 p hg
    simpa only [d8126, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43242 p hg
    simpa only [d8126, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43244 (p : Pattern) (guard : d8132 p = 1) : d2629 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43243 p hg
    simpa only [d8132, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43091 p hg
    simpa only [d8132, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43245 (p : Pattern) (guard : d8112 p = 1) : d2614 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42356 p hg
    simpa only [d8112, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42463 p hg
    simpa only [d8112, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43246 (p : Pattern) (guard : d8118 p = 1) : d2615 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43245 p hg
    simpa only [d8118, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43247 (p : Pattern) (guard : d8124 p = 1) : d2616 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43246 p hg
    simpa only [d8124, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43248 (p : Pattern) (guard : d8125 p = 1) : d2617 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43109 p hg
    simpa only [d8125, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43247 p hg
    simpa only [d8125, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43249 (p : Pattern) (guard : d8130 p = 1) : d2627 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43137 p hg
    simpa only [d8130, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42485 p hg
    simpa only [d8130, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43250 (p : Pattern) (guard : d8131 p = 1) : d2628 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43248 p hg
    simpa only [d8131, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43249 p hg
    simpa only [d8131, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43251 (p : Pattern) (guard : d8106 p = 1) : d2607 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42544 p hg
    simpa only [d8106, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42026 p hg
    simpa only [d8106, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43252 (p : Pattern) (guard : d8112 p = 1) : d2630 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43251 p hg
    simpa only [d8112, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42222 p hg
    simpa only [d8112, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43253 (p : Pattern) (guard : d8118 p = 1) : d2631 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43252 p hg
    simpa only [d8118, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43254 (p : Pattern) (guard : d8124 p = 1) : d2633 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43253 p hg
    simpa only [d8124, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43095 p hg
    simpa only [d8124, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43255 (p : Pattern) (guard : d8130 p = 1) : d2635 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43254 p hg
    simpa only [d8130, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43097 p hg
    simpa only [d8130, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43256 (p : Pattern) (guard : d8123 p = 1) : d2632 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43234 p hg
    simpa only [d8123, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43257 (p : Pattern) (guard : d8129 p = 1) : d2634 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43256 p hg
    simpa only [d8129, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43258 (p : Pattern) (guard : d8135 p = 1) : d2636 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43257 p hg
    simpa only [d8135, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43259 (p : Pattern) (guard : d8136 p = 1) : d2637 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43255 p hg
    simpa only [d8136, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43258 p hg
    simpa only [d8136, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
