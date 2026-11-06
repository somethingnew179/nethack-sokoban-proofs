/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons339
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47600 (p : Pattern) (guard : d8118 p = 1) : d3045 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3045, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47597 p hg
    simpa only [d8118, d3045, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3045, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47599 p hg
    simpa only [d8118, d3045, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47601 (p : Pattern) (guard : d8123 p = 1) : d3046 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3046, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47577 p hg
    simpa only [d8123, d3046, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3046, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47115 p hg
    simpa only [d8123, d3046, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47602 (p : Pattern) (guard : d8124 p = 1) : d3047 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3047, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47600 p hg
    simpa only [d8124, d3047, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3047, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47601 p hg
    simpa only [d8124, d3047, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47603 (p : Pattern) (guard : d8117 p = 1) : d3051 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3051, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47010 p hg
    simpa only [d8117, d3051, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3051, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47119 p hg
    simpa only [d8117, d3051, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47604 (p : Pattern) (guard : d8123 p = 1) : d3052 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3052, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47603 p hg
    simpa only [d8123, d3052, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3052, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3052, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47605 (p : Pattern) (guard : d8129 p = 1) : d3053 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3053, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47604 p hg
    simpa only [d8129, d3053, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3053, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3053, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47606 (p : Pattern) (guard : d8130 p = 1) : d3054 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3054, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47602 p hg
    simpa only [d8130, d3054, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3054, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47605 p hg
    simpa only [d8130, d3054, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47607 (p : Pattern) (guard : d8105 p = 1) : d3039 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3039, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35818 p hg
    simpa only [d8105, d3039, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3039, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24078 p hg
    simpa only [d8105, d3039, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47608 (p : Pattern) (guard : d8111 p = 1) : d3040 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3040, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47607 p hg
    simpa only [d8111, d3040, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3040, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d3040, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47609 (p : Pattern) (guard : d0 p = 1) : d3048 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47610 (p : Pattern) (guard : d8117 p = 1) : d3055 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3055, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47608 p hg
    simpa only [d8117, d3055, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3055, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47609 p hg
    simpa only [d8117, d3055, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47611 (p : Pattern) (guard : d0 p = 1) : d3151 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47612 (p : Pattern) (guard : d8123 p = 1) : d3152 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3152, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47610 p hg
    simpa only [d8123, d3152, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3152, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47611 p hg
    simpa only [d8123, d3152, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47613 (p : Pattern) (guard : d8129 p = 1) : d3154 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3154, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47612 p hg
    simpa only [d8129, d3154, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3154, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47590 p hg
    simpa only [d8129, d3154, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47614 (p : Pattern) (guard : d8135 p = 1) : d3155 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3155, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47613 p hg
    simpa only [d8135, d3155, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3155, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47132 p hg
    simpa only [d8135, d3155, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47615 (p : Pattern) (guard : d8136 p = 1) : d3156 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3156, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47606 p hg
    simpa only [d8136, d3156, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3156, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47614 p hg
    simpa only [d8136, d3156, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47616 (p : Pattern) (guard : d8123 p = 1) : d3067 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3067, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47536 p hg
    simpa only [d8123, d3067, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3067, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3067, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47617 (p : Pattern) (guard : d8129 p = 1) : d3068 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3068, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47616 p hg
    simpa only [d8129, d3068, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3068, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3068, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47618 (p : Pattern) (guard : d8135 p = 1) : d3069 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3069, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47617 p hg
    simpa only [d8135, d3069, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3069, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d3069, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47619 (p : Pattern) (guard : d8141 p = 1) : d3070 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d3070, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47618 p hg
    simpa only [d8141, d3070, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d3070, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8141, d3070, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47620 (p : Pattern) (guard : d8142 p = 1) : d3158 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3158, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47615 p hg
    simpa only [d8142, d3158, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3158, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47619 p hg
    simpa only [d8142, d3158, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47621 (p : Pattern) (guard : d8143 p = 1) : d3159 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3159, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47594 p hg
    simpa only [d8143, d3159, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3159, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47620 p hg
    simpa only [d8143, d3159, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47622 (p : Pattern) (guard : d8100 p = 1) : d3033 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3033, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35703 p hg
    simpa only [d8100, d3033, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3033, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47105 p hg
    simpa only [d8100, d3033, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47623 (p : Pattern) (guard : d8106 p = 1) : d3034 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3034, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47622 p hg
    simpa only [d8106, d3034, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3034, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39883 p hg
    simpa only [d8106, d3034, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47624 (p : Pattern) (guard : d8105 p = 1) : d3033 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3033, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35818 p hg
    simpa only [d8105, d3033, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3033, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24075 p hg
    simpa only [d8105, d3033, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47625 (p : Pattern) (guard : d8111 p = 1) : d3034 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3034, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47624 p hg
    simpa only [d8111, d3034, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3034, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15465 p hg
    simpa only [d8111, d3034, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47626 (p : Pattern) (guard : d8112 p = 1) : d3034 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47623 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47625 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47627 (p : Pattern) (guard : d8105 p = 1) : d3160 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3160, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35795 p hg
    simpa only [d8105, d3160, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3160, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24210 p hg
    simpa only [d8105, d3160, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47628 (p : Pattern) (guard : d8111 p = 1) : d3161 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3161, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47627 p hg
    simpa only [d8111, d3161, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3161, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15603 p hg
    simpa only [d8111, d3161, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47629 (p : Pattern) (guard : d0 p = 1) : d3043 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47630 (p : Pattern) (guard : d8117 p = 1) : d3162 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3162, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47628 p hg
    simpa only [d8117, d3162, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3162, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47629 p hg
    simpa only [d8117, d3162, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47631 (p : Pattern) (guard : d8118 p = 1) : d3163 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3163, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47626 p hg
    simpa only [d8118, d3163, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3163, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47630 p hg
    simpa only [d8118, d3163, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47632 (p : Pattern) (guard : d8117 p = 1) : d3164 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3164, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47574 p hg
    simpa only [d8117, d3164, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3164, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47112 p hg
    simpa only [d8117, d3164, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47633 (p : Pattern) (guard : d8123 p = 1) : d3165 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3165, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47632 p hg
    simpa only [d8123, d3165, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3165, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47115 p hg
    simpa only [d8123, d3165, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47634 (p : Pattern) (guard : d8124 p = 1) : d3166 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3166, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47631 p hg
    simpa only [d8124, d3166, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3166, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47633 p hg
    simpa only [d8124, d3166, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47635 (p : Pattern) (guard : d0 p = 1) : d3167 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47636 (p : Pattern) (guard : d8117 p = 1) : d3168 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3168, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47041 p hg
    simpa only [d8117, d3168, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3168, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47635 p hg
    simpa only [d8117, d3168, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47637 (p : Pattern) (guard : d8123 p = 1) : d3169 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3169, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47636 p hg
    simpa only [d8123, d3169, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3169, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47565 p hg
    simpa only [d8123, d3169, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47638 (p : Pattern) (guard : d0 p = 1) : d3172 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47639 (p : Pattern) (guard : d8129 p = 1) : d3173 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3173, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47637 p hg
    simpa only [d8129, d3173, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3173, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47638 p hg
    simpa only [d8129, d3173, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47640 (p : Pattern) (guard : d8130 p = 1) : d3174 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3174, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47634 p hg
    simpa only [d8130, d3174, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3174, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47639 p hg
    simpa only [d8130, d3174, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47641 (p : Pattern) (guard : d8105 p = 1) : d3160 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3160, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35836 p hg
    simpa only [d8105, d3160, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3160, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24210 p hg
    simpa only [d8105, d3160, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47642 (p : Pattern) (guard : d8111 p = 1) : d3161 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3161, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47641 p hg
    simpa only [d8111, d3161, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3161, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15603 p hg
    simpa only [d8111, d3161, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47643 (p : Pattern) (guard : d0 p = 1) : d3178 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47644 (p : Pattern) (guard : d8117 p = 1) : d3179 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3179, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47642 p hg
    simpa only [d8117, d3179, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3179, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47643 p hg
    simpa only [d8117, d3179, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47645 (p : Pattern) (guard : d0 p = 1) : d3182 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47646 (p : Pattern) (guard : d8123 p = 1) : d3183 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3183, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47644 p hg
    simpa only [d8123, d3183, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3183, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47645 p hg
    simpa only [d8123, d3183, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47647 (p : Pattern) (guard : d0 p = 1) : d3186 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47648 (p : Pattern) (guard : d8129 p = 1) : d3187 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3187, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47646 p hg
    simpa only [d8129, d3187, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3187, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47647 p hg
    simpa only [d8129, d3187, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47649 (p : Pattern) (guard : d0 p = 1) : d3192 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47650 (p : Pattern) (guard : d8135 p = 1) : d3193 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3193, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47648 p hg
    simpa only [d8135, d3193, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3193, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47649 p hg
    simpa only [d8135, d3193, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47651 (p : Pattern) (guard : d8136 p = 1) : d3194 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3194, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47640 p hg
    simpa only [d8136, d3194, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3194, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47650 p hg
    simpa only [d8136, d3194, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47652 (p : Pattern) (guard : d0 p = 1) : d3042 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47653 (p : Pattern) (guard : d8117 p = 1) : d3195 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3195, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47574 p hg
    simpa only [d8117, d3195, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3195, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47652 p hg
    simpa only [d8117, d3195, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47654 (p : Pattern) (guard : d0 p = 1) : d3196 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47655 (p : Pattern) (guard : d8123 p = 1) : d3197 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3197, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47653 p hg
    simpa only [d8123, d3197, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3197, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47654 p hg
    simpa only [d8123, d3197, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47656 (p : Pattern) (guard : d8129 p = 1) : d3198 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3198, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47655 p hg
    simpa only [d8129, d3198, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3198, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47130 p hg
    simpa only [d8129, d3198, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47657 (p : Pattern) (guard : d8135 p = 1) : d3199 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3199, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47656 p hg
    simpa only [d8135, d3199, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3199, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47132 p hg
    simpa only [d8135, d3199, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47658 (p : Pattern) (guard : d0 p = 1) : d3206 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47659 (p : Pattern) (guard : d8141 p = 1) : d3207 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d3207, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47657 p hg
    simpa only [d8141, d3207, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d3207, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47658 p hg
    simpa only [d8141, d3207, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47660 (p : Pattern) (guard : d8142 p = 1) : d3208 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3208, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47651 p hg
    simpa only [d8142, d3208, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3208, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47659 p hg
    simpa only [d8142, d3208, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47661 (p : Pattern) (guard : d0 p = 1) : d3042 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47662 (p : Pattern) (guard : d8117 p = 1) : d3195 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3195, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47585 p hg
    simpa only [d8117, d3195, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3195, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47661 p hg
    simpa only [d8117, d3195, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47663 (p : Pattern) (guard : d0 p = 1) : d3209 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47664 (p : Pattern) (guard : d8123 p = 1) : d3210 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3210, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47662 p hg
    simpa only [d8123, d3210, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3210, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47663 p hg
    simpa only [d8123, d3210, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47665 (p : Pattern) (guard : d0 p = 1) : d3212 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47666 (p : Pattern) (guard : d8129 p = 1) : d3213 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3213, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47664 p hg
    simpa only [d8129, d3213, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3213, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47665 p hg
    simpa only [d8129, d3213, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47667 (p : Pattern) (guard : d0 p = 1) : d3216 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47668 (p : Pattern) (guard : d8135 p = 1) : d3217 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3217, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47666 p hg
    simpa only [d8135, d3217, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3217, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47667 p hg
    simpa only [d8135, d3217, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47669 (p : Pattern) (guard : d0 p = 1) : d3206 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47670 (p : Pattern) (guard : d8141 p = 1) : d3218 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d3218, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47668 p hg
    simpa only [d8141, d3218, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d3218, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47669 p hg
    simpa only [d8141, d3218, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47671 (p : Pattern) (guard : d8147 p = 1) : d3219 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d3219, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47670 p hg
    simpa only [d8147, d3219, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d3219, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d3219, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47672 (p : Pattern) (guard : d8148 p = 1) : d3220 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d3220, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47660 p hg
    simpa only [d8148, d3220, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d3220, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47671 p hg
    simpa only [d8148, d3220, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47673 (p : Pattern) (guard : d8149 p = 1) : d3221 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d3221, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47621 p hg
    simpa only [d8149, d3221, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d3221, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47672 p hg
    simpa only [d8149, d3221, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47674 (p : Pattern) (guard : d8150 p = 1) : d3222 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d3222, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47519 p hg
    simpa only [d8150, d3222, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d3222, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47673 p hg
    simpa only [d8150, d3222, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47675 (p : Pattern) (guard : d8151 p = 1) : d3223 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47347 p hg
    simpa only [d8151, d3223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47674 p hg
    simpa only [d8151, d3223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47676 (p : Pattern) (guard : d8152 p = 1) : d3224 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47153 p hg
    simpa only [d8152, d3224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47675 p hg
    simpa only [d8152, d3224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47677 (p : Pattern) (guard : d8096 p = 1) : d33 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34519 p hg
    simpa only [d8096, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47678 (p : Pattern) (guard : d8097 p = 1) : d950 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34377 p hg
    simpa only [d8097, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47677 p hg
    simpa only [d8097, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47679 (p : Pattern) (guard : d8103 p = 1) : d1399 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47678 p hg
    simpa only [d8103, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34400 p hg
    simpa only [d8103, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47680 (p : Pattern) (guard : d8104 p = 1) : d1400 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34371 p hg
    simpa only [d8104, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47679 p hg
    simpa only [d8104, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47681 (p : Pattern) (guard : d8097 p = 1) : d33 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34412 p hg
    simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34635 p hg
    simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47682 (p : Pattern) (guard : d8103 p = 1) : d1401 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47681 p hg
    simpa only [d8103, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34445 p hg
    simpa only [d8103, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47683 (p : Pattern) (guard : d8109 p = 1) : d1402 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47682 p hg
    simpa only [d8109, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34457 p hg
    simpa only [d8109, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47684 (p : Pattern) (guard : d8110 p = 1) : d1403 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47680 p hg
    simpa only [d8110, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47683 p hg
    simpa only [d8110, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47685 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34784 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47686 (p : Pattern) (guard : d8086 p = 1) : d31 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47685 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47687 (p : Pattern) (guard : d8091 p = 1) : d31 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47686 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47688 (p : Pattern) (guard : d8096 p = 1) : d53 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47687 p hg
    simpa only [d8096, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47689 (p : Pattern) (guard : d8101 p = 1) : d360 p ≤ (0 : Int) + d360 p := by
  omega
theorem compare47690 (p : Pattern) (guard : d8102 p = 1) : d1165 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47688 p hg
    simpa only [d8102, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47689 p hg
    simpa only [d8102, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47691 (p : Pattern) (guard : d8103 p = 1) : d1404 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34478 p hg
    simpa only [d8103, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47690 p hg
    simpa only [d8103, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47692 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare950 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47693 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47692 p hg
    simpa only [d31, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d31, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47694 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47693 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47695 (p : Pattern) (guard : d8086 p = 1) : d31 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47694 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47696 (p : Pattern) (guard : d8091 p = 1) : d31 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47695 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47697 (p : Pattern) (guard : d8096 p = 1) : d53 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47696 p hg
    simpa only [d8096, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47698 (p : Pattern) (guard : d8101 p = 1) : d795 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34588 p hg
    simpa only [d8101, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47699 (p : Pattern) (guard : d8102 p = 1) : d796 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47697 p hg
    simpa only [d8102, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47698 p hg
    simpa only [d8102, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47700 (p : Pattern) (guard : d8108 p = 1) : d1405 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47699 p hg
    simpa only [d8108, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34515 p hg
    simpa only [d8108, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47701 (p : Pattern) (guard : d8109 p = 1) : d1406 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47691 p hg
    simpa only [d8109, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47700 p hg
    simpa only [d8109, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47702 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34657 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47703 (p : Pattern) (guard : d8086 p = 1) : d31 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47702 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47704 (p : Pattern) (guard : d8091 p = 1) : d31 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47703 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47705 (p : Pattern) (guard : d8096 p = 1) : d53 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47704 p hg
    simpa only [d8096, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47706 (p : Pattern) (guard : d8101 p = 1) : d795 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34527 p hg
    simpa only [d8101, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47707 (p : Pattern) (guard : d8102 p = 1) : d796 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47705 p hg
    simpa only [d8102, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47706 p hg
    simpa only [d8102, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47708 (p : Pattern) (guard : d8107 p = 1) : d1171 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43662 p hg
    simpa only [d8107, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47709 (p : Pattern) (guard : d8108 p = 1) : d1407 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47707 p hg
    simpa only [d8108, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47708 p hg
    simpa only [d8108, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47710 (p : Pattern) (guard : d8114 p = 1) : d1408 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47709 p hg
    simpa only [d8114, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43665 p hg
    simpa only [d8114, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47711 (p : Pattern) (guard : d8115 p = 1) : d1409 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47701 p hg
    simpa only [d8115, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47710 p hg
    simpa only [d8115, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47712 (p : Pattern) (guard : d8116 p = 1) : d1410 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47684 p hg
    simpa only [d8116, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47711 p hg
    simpa only [d8116, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47713 (p : Pattern) (guard : d8102 p = 1) : d54 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34557 p hg
    simpa only [d8102, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d8102, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47714 (p : Pattern) (guard : d8108 p = 1) : d1411 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47713 p hg
    simpa only [d8108, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47715 (p : Pattern) (guard : d8109 p = 1) : d1412 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34556 p hg
    simpa only [d8109, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47714 p hg
    simpa only [d8109, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47716 (p : Pattern) (guard : d8102 p = 1) : d53 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34566 p hg
    simpa only [d8102, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d8102, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47717 (p : Pattern) (guard : d8108 p = 1) : d1413 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47716 p hg
    simpa only [d8108, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8108, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47718 (p : Pattern) (guard : d8114 p = 1) : d1414 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47717 p hg
    simpa only [d8114, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47719 (p : Pattern) (guard : d8115 p = 1) : d1415 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47715 p hg
    simpa only [d8115, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47718 p hg
    simpa only [d8115, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47720 (p : Pattern) (guard : d8107 p = 1) : d1181 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d8107, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47721 (p : Pattern) (guard : d8108 p = 1) : d1416 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34591 p hg
    simpa only [d8108, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47720 p hg
    simpa only [d8108, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47722 (p : Pattern) (guard : d8107 p = 1) : d808 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d8107, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d8107, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47723 (p : Pattern) (guard : d8113 p = 1) : d1417 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47722 p hg
    simpa only [d8113, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47724 (p : Pattern) (guard : d8114 p = 1) : d1418 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47721 p hg
    simpa only [d8114, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47723 p hg
    simpa only [d8114, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47725 (p : Pattern) (guard : d8113 p = 1) : d972 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47722 p hg
    simpa only [d8113, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47726 (p : Pattern) (guard : d8119 p = 1) : d974 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47725 p hg
    simpa only [d8119, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47727 (p : Pattern) (guard : d8120 p = 1) : d1419 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47724 p hg
    simpa only [d8120, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47726 p hg
    simpa only [d8120, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47728 (p : Pattern) (guard : d8121 p = 1) : d1420 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47719 p hg
    simpa only [d8121, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47727 p hg
    simpa only [d8121, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47729 (p : Pattern) (guard : d8122 p = 1) : d1421 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47712 p hg
    simpa only [d8122, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47728 p hg
    simpa only [d8122, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47730 (p : Pattern) (guard : d8102 p = 1) : d54 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34552 p hg
    simpa only [d8102, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d8102, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47731 (p : Pattern) (guard : d8108 p = 1) : d1411 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47730 p hg
    simpa only [d8108, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47732 (p : Pattern) (guard : d8109 p = 1) : d1412 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38104 p hg
    simpa only [d8109, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47731 p hg
    simpa only [d8109, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47733 (p : Pattern) (guard : d8102 p = 1) : d53 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38110 p hg
    simpa only [d8102, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d8102, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47734 (p : Pattern) (guard : d8108 p = 1) : d1413 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47733 p hg
    simpa only [d8108, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8108, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47735 (p : Pattern) (guard : d8114 p = 1) : d1414 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47734 p hg
    simpa only [d8114, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47736 (p : Pattern) (guard : d8115 p = 1) : d1415 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47732 p hg
    simpa only [d8115, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47735 p hg
    simpa only [d8115, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47737 (p : Pattern) (guard : d8107 p = 1) : d1181 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34590 p hg
    simpa only [d8107, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47738 (p : Pattern) (guard : d8108 p = 1) : d1416 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41378 p hg
    simpa only [d8108, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47737 p hg
    simpa only [d8108, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47739 (p : Pattern) (guard : d8107 p = 1) : d808 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d8107, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d8107, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
